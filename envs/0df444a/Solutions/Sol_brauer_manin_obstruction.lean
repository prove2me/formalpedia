-- Prove2me | solution 1 for brauer_manin_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:39:27.701807+00:00
-- url     : https://prove2.me/submissions/cee55f2c-b02b-45b9-9a7d-d0af8a9f9497

import Mathlib

theorem solution (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (f g : MvPolynomial (Fin n) ℤ) :
    (∃ x : Fin n → K, MvPolynomial.eval x (f.map (algebraMap ℤ K)) = 0 ∧
      MvPolynomial.eval x (g.map (algebraMap ℤ K)) = 0) →
    ∃ C : ℝ, C ≥ 0 :=
  fun _ => ⟨0, le_refl 0⟩
