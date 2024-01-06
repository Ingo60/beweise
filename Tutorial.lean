import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic


--- "and" is commutative
theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

theorem and_either_way (p q : Prop) : p ∧ q ↔ q ∧ p := by
  have h₁ : p ∧ q → q ∧ p :=  by exact and_commutative p q
  have h₂ : q ∧ p → p ∧ q :=  by exact and_commutative q p
  exact Iff.intro h₁ h₂

-- #print Nat.add_comm
example : p ∨ q ↔ q ∨ p := Iff.intro
  (fun p_or_q => p_or_q.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))
  (fun q_or_p => q_or_p.elim (fun hq => Or.inr hq) (fun hp => Or.inl hp))

example : p ∨ q ↔ q ∨ p := by
  have h₁ (a b: Prop): a ∨ b → b ∨ a := by
    intro a_or_b
    apply a_or_b.elim
    intro ha
    exact Or.inr ha
    intro hb
    exact Or.inl hb
  exact Iff.intro (h₁ p q) (h₁ q p)

theorem equation_add : ∀a b n: Nat  , (a+n = b+n) → (a = b) := by
  intro a
  intro b
  intro n
  induction n with
    | zero => {
      rw [a.add_zero, b.add_zero]
      tauto
    }
    | succ d h => {
      rw [a.add_succ, b.add_succ]
      intro hs
      apply h
      apply Nat.succ_inj'.mp
      assumption
    }
