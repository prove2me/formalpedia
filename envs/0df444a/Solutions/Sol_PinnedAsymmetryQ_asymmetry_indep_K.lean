-- Prove2me | solution 1 for PinnedAsymmetryQ.asymmetry_indep_K
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T04:28:57.243734+00:00
-- url     : https://prove2.me/submissions/60d8c27e-6a10-47c9-ab95-5066370a04ca

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

namespace PinnedAsymmetryQSol
open PinnedAsymmetryQ

theorem radicand_flip (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ) :
    (β * c * sin (flip0 q k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (flip0 q k a))
      = (β * c * sin (k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (k a)) := by
  have hs : ∑ a : Fin q, (1 - cos (flip0 q k a)) = ∑ a : Fin q, (1 - cos (k a)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · subst ha; simp [flip0]
    · simp [flip0, ha]
  rw [hs, show flip0 q k 0 = -(k 0) by simp [flip0], sin_neg]
  ring

theorem omega_is_root (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ)
    (h : 0 ≤ (β * c * sin (k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (k a))) :
    (omega q K c β k) ^ 2 - 2 * β * c * sin (k 0) * omega q K c β k
      - (K + 2 * c * ∑ a : Fin q, (1 - cos (k a))) = 0 := by
  unfold omega
  have hs := Real.sq_sqrt h
  nlinarith [hs]

theorem asymmetry (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ) :
    omega q K c β k - omega q K c β (flip0 q k) = 2 * β * c * sin (k 0) := by
  unfold omega
  rw [radicand_flip, show flip0 q k 0 = -(k 0) by simp [flip0], sin_neg]
  ring

end PinnedAsymmetryQSol

open PinnedAsymmetryQ PinnedAsymmetryQSol

theorem solution (q : ℕ) [NeZero q] (K₁ K₂ c β : ℝ) (k : Fin q → ℝ) :
    omega q K₁ c β k - omega q K₁ c β (flip0 q k)
      = omega q K₂ c β k - omega q K₂ c β (flip0 q k) := by
  rw [asymmetry, asymmetry]
