-- Prove2me | solution 1 for ShortWDRODual.IP.lemma_EC_1_setfun
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T13:51:51.631768+00:00
-- url     : https://prove2.me/submissions/6d02068e-f736-4b31-b3e3-e2608237a5c4

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_IP_Setting

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

open ShortWDRODual.IP in
theorem solution {X : Type*} [MeasurableSpace X] (E : X → Set X)
    (hE : ∀ xh, MeasurableSet (E xh) ∧ (E xh).Nonempty) :
    DiagDomSetFun E ↔ DiagDomSet (graph E) := by
  constructor
  · rintro ⟨-, hm, hd⟩
    exact ⟨hm, fun xh x h => hd xh x h⟩
  · rintro ⟨hm, hd⟩
    exact ⟨hE, hm, fun xh x h => hd xh x h⟩
