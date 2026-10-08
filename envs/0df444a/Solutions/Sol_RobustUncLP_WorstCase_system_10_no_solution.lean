-- Prove2me | solution 1 for RobustUncLP.WorstCase.system_10_no_solution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:14:50.250817+00:00
-- url     : https://prove2.me/submissions/dde42d5f-84d7-4191-b383-60a5be87b134

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting

set_option autoImplicit false

open Matrix

open Matrix RobustUncLP.WorstCase in
theorem solution {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (f : Fin n → ℝ) (Q : Set (Fin n → ℝ)) (hQ : ∀ A ∈ U, instFeas f A ⊆ Q)
    {N : ℕ} (hN : 0 < N) (A : Fin N → Matrix (Fin m) (Fin n) ℝ) (hA : ∀ p, A p ∈ U)
    (hinQ : ∀ x ∈ Q, ¬ ((∀ p, 0 ≤ A p *ᵥ x) ∧ f ⬝ᵥ x = 1)) :
    ¬ ∃ x : Fin n → ℝ, (∀ p, 0 ≤ A p *ᵥ x) ∧ f ⬝ᵥ x = 1 := by
  rintro ⟨x, hx, hf⟩
  have hxQ : x ∈ Q := hQ (A ⟨0, hN⟩) (hA _) ⟨hx _, hf⟩
  exact hinQ x hxQ ⟨hx, hf⟩
