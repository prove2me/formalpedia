-- Prove2me | solution 1 for StableVotingDistortion.Lemma9Reduction.canonicalFirst
-- status  : ACCEPTED   (prove)
-- author  : @a142857a
-- created : 2026-11-14T19:00:45.31623+00:00
-- url     : https://prove2.me/submissions/ce892532-dc05-40ce-a59e-92b9db632842

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalFirstLowerRanks
import Theorems.Thm_StableVotingDistortion_Lemma9Reduction_canonicalFirstUpperRanks
open StableVotingDistortion StableVotingDistortion.PaperMiddle StableVotingDistortion.PaperCurve StableVotingDistortion.PaperBox StableVotingDistortion.Lemma9Reduction Set
theorem solution {p q : ℝ} (hp : p ∈ Icc (16/25:ℝ) (99/100)) (hq : q ∈ Icc (0:ℝ) PaperCurve.lam) : q+PaperMiddle.canonical score p*deltaP score p q ≤ PaperCurve.lam := by
  by_cases h : q ≤ (703/2500:ℝ)
  · exact canonicalFirstLowerRanks hp ⟨hq.1,h⟩
  · exact canonicalFirstUpperRanks hp ⟨le_of_not_ge h,hq.2⟩
