-- Prove2me | solution 1 for YieldPostpone.Pricing.dr_threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T05:17:04.984717+00:00
-- url     : https://prove2.me/submissions/e1a98b5a-bcf3-41e5-ab84-9718b7a01ee5

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Interplay_threshold_order

open YieldPostpone.Pricing

theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cDR1 P < cDR2 P ∧ cDR2 P < cDA P := by
  have H := YieldPostpone.Interplay.threshold_order ⟨P.a, P.b, P.α, P.θ⟩ hP hα
  exact H.2
