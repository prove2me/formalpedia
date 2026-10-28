-- Prove2me | solution 1 for ShortWDRODual.IP.lemma_EC_1_set
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:48:32.185+00:00
-- url     : https://prove2.me/submissions/bd9bd4bf-27de-4eb7-bd6c-08e790ea2003

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

open ShortWDRODual.IP in
theorem solution {X : Type*} [MeasurableSpace X] (A : Set (X × X)) :
    DiagDomSet A ↔ DiagDomFun (A.indicator (fun _ => (1 : EReal))) := by
  have : NeZero (1 : EReal) := ⟨by norm_num⟩
  constructor
  · rintro ⟨hm, hd⟩
    refine ⟨(measurable_indicator_const_iff (1 : EReal)).mpr hm, fun xh x => ?_⟩
    by_cases h : (xh, x) ∈ A
    · simp [Set.indicator, h, hd xh x h]
    · simp only [Set.indicator, h, if_false]
      split_ifs <;> norm_num
  · rintro ⟨hm, hd⟩
    refine ⟨(measurable_indicator_const_iff (1 : EReal)).mp hm, fun xh x h => ?_⟩
    by_contra h2
    have := hd xh x
    simp only [Set.indicator, h, h2, if_true, if_false] at this
    exact (not_le.mpr (zero_lt_one : (0:EReal) < 1)) this
