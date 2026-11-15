-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.firstLow
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:41:53.856335+00:00
-- url     : https://prove2.me/submissions/703aa73a-b35b-42fa-8679-b0886b80da90

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_firstLowPrimitiveAtZero
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_firstLowCorrectionBudget
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
open StableVotingDistortion.Lemma9Reduction
theorem solution {p q x : ℝ} (hp : p ∈ Icc (3/50:ℝ) (16/25)) (hq : q ∈ Icc (0:ℝ) p) (hx : x ∈ Icc (0:ℝ) PaperCurve.lam) : lowFirst PaperCurve.lam score (entry PaperMiddle.Knot.beta p) (-1) (entry PaperMiddle.Knot.eta p) p q x ≤ 0 := by
  have h₁ := firstLowPrimitiveAtZero hp hq
  have h₂ := firstLowCorrectionBudget hp hx
  unfold lowFirst correction
  rw [show (-1:ℝ) * (PaperCurve.lam-x) + entry PaperMiddle.Knot.eta p * score x =
    entry PaperMiddle.Knot.eta p * score x+x-PaperCurve.lam by ring]
  linarith only [h₁,h₂]
