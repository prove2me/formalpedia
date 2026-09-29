-- Prove2me | solution 1 for PinnedAsymmetryQ.radicand_flip
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T04:28:23.575984+00:00
-- url     : https://prove2.me/submissions/45f1e9c1-622a-47b7-8cb8-3682296eecc2

import Mathlib
import Definitions.Def_PinnedAsymmetryQ_omega

open Real BigOperators

open PinnedAsymmetryQ

theorem solution (q : ℕ) [NeZero q] (K c β : ℝ) (k : Fin q → ℝ) :
    (β * c * sin (flip0 q k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (flip0 q k a))
      = (β * c * sin (k 0)) ^ 2 + K + 2 * c * ∑ a : Fin q, (1 - cos (k a)) := by
  have hs : ∑ a : Fin q, (1 - cos (flip0 q k a)) = ∑ a : Fin q, (1 - cos (k a)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · subst ha; simp [flip0]
    · simp [flip0, ha]
  rw [hs, show flip0 q k 0 = -(k 0) by simp [flip0], sin_neg]
  ring
