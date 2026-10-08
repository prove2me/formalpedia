-- Prove2me | solution 1 for TaoAnDCA.Restart.restart_case_a
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:46:58.203931+00:00
-- url     : https://prove2.me/submissions/a7417098-5a94-4ccb-822d-f15182c149bf

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) (hb : 0 < inner ℝ b xs) :
    ‖-xs‖ ≤ r ∧
      TaoAnDCA.TRS.quad A b (-xs) = TaoAnDCA.TRS.quad A b xs + 2 * inner ℝ (A xs + lamStar • xs) xs ∧
      TaoAnDCA.TRS.quad A b xs + 2 * inner ℝ (A xs + lamStar • xs) xs = TaoAnDCA.TRS.quad A b xs - 2 * inner ℝ b xs ∧
      TaoAnDCA.TRS.quad A b (-xs) < TaoAnDCA.TRS.quad A b xs := by
  rcases hkkt with ⟨_, hs, _, hf⟩
  have he : TaoAnDCA.TRS.quad A b (-xs) = TaoAnDCA.TRS.quad A b xs - 2 * inner ℝ b xs := by
    simp only [TaoAnDCA.TRS.quad, map_neg, inner_neg_left, inner_neg_right]
    ring
  have hi : inner ℝ (A xs + lamStar • xs) xs = -inner ℝ b xs := by
    rw [hs, inner_neg_left]
  refine ⟨by simpa using hf, ?_, ?_, ?_⟩
  · rw [he, hi]; ring
  · rw [hi]; ring
  · rw [he]; linarith

#print axioms solution
