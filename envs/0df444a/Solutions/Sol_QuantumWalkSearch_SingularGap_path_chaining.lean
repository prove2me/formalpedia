-- Prove2me | solution 1 for QuantumWalkSearch.SingularGap.path_chaining
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:57:11.622997+00:00
-- url     : https://prove2.me/submissions/e63e6873-1a32-4f31-bb01-f8b6c932017f

import Mathlib
import Definitions.Def_QuantumWalkSearch_SingularGap_Discriminant

set_option autoImplicit false

open Matrix QuantumWalkSearch.SingularGap

theorem solution {X : Type*} [Fintype X] [DecidableEq X]
    (P : Matrix X X ℝ) (π : X → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ X) (hirr : P.IsIrreducible)
    (hπ : IsStationaryDistribution P π)
    (u : X → ℂ)
    (hu : ∀ x y : X, 0 < P x y → u y = u x * ((Real.sqrt (π y / π x) : ℝ) : ℂ)) :
    ∀ x₁ y : X, u y = u x₁ * ((Real.sqrt (π y / π x₁) : ℝ) : ℂ) := by
  have key : ∀ a b : X, ∀ p : @Quiver.Path X (Matrix.toQuiver P) a b,
      u b = u a * ((Real.sqrt (π b / π a) : ℝ) : ℂ) := by
    intro a b p
    induction p with
    | nil => simp [div_self (hπ.pos a).ne']
    | @cons b' c p e ih =>
      have h1 := hu b' c e.down
      rw [h1, ih, mul_assoc, ← Complex.ofReal_mul, ← Real.sqrt_mul (div_nonneg (hπ.pos b').le (hπ.pos a).le)]
      congr 3
      have := (hπ.pos a).ne'
      have := (hπ.pos b').ne'
      field_simp
  intro x₁ y
  obtain ⟨p, _⟩ := hirr.connected x₁ y
  exact key x₁ y p
