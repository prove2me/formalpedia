-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.verifiedCanonicalSecond
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T18:48:32.340212+00:00
-- url     : https://prove2.me/submissions/c5a73149-62ab-4430-a182-44314f50f7fb

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalSecondLowerRanks
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalSecondUpperRanks
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox Set
theorem solution {p q z : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) PaperCurve.lam) (hz : z ∈ Icc p 1) : highSecond PaperCurve.lam score (canonical score p) 1 (-(canonical score p*(1-p))) p q z 1 ≤ 0 := by
  by_cases h : q ≤ (703/2500:ℝ)
  · exact StableVotingDistortion.Lemma9Reduction.canonicalSecondLowerRanks hp ⟨hq.1,h⟩ hz
  · exact StableVotingDistortion.Lemma9Reduction.canonicalSecondUpperRanks hp ⟨le_of_not_ge h,hq.2⟩ hz
