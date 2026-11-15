-- Prove2me | solution 1 for StableVotingDistortion.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:41:48.227952+00:00
-- url     : https://prove2.me/submissions/48ede848-2cee-4683-9edd-39359b9beb2e

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_verifiedNamedScore
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem solution :
    ∃ (lam : ℝ) (ϕ β : ℝ → ℝ) (c : ℝ → ℝ → ℝ),
      VerifierHypotheses lam ϕ β c ∧ 1 + 2 * lam ≤ 2.1248 := by
  exact ⟨PaperMiddle.lam, score, beta score, corr score, StableVotingDistortion.Lemma9Reduction.verifiedNamedScore.1, StableVotingDistortion.Lemma9Reduction.verifiedNamedScore.2.le⟩
