-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.proposition_6_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T21:34:22.898822+00:00
-- url     : https://prove2.me/submissions/0e13e66b-da83-44bd-913b-e4eba1191e5a

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting
import Definitions.Def_PrivSeqLearn_QueryComplexity_OB
import Theorems.Thm_PrivSeqLearn_QueryComplexity_ob_accurate
import Theorems.Thm_PrivSeqLearn_QueryComplexity_claim_6_3
import Theorems.Thm_PrivSeqLearn_QueryComplexity_claim_6_4
import Theorems.Thm_PrivSeqLearn_QueryComplexity_coverNumber_mono

open PrivSeqLearn.QueryComplexity

theorem solution (ϵ δ : ℝ) (L : ℕ) (hϵ : 0 < ϵ) (hδ : 0 < δ) (hL : 2 ≤ L)
    (h2ϵδ : 2 * ϵ < δ) (hδL : δ ≤ 1 / (L : ℝ)) :
    IsPrivate ϵ δ L (obStrategy ϵ L (by omega)) := by
  have hϵL : 2 * ϵ < 1 / (L : ℝ) := lt_of_lt_of_le h2ϵδ hδL
  refine ⟨ob_accurate ϵ L hϵ hL hϵL, ?_⟩
  intro x hx q hq
  exact coverNumber_mono δ L (guessUnion ϵ L) _ hδ (claim_6_4 ϵ L hϵ hL hϵL x hx q hq)
    ((Metric.isBounded_Ico (0 : ℝ) 1).subset (fun z hz => hz.1))
    (claim_6_3 ϵ δ L hϵ hδ hL h2ϵδ hδL)
