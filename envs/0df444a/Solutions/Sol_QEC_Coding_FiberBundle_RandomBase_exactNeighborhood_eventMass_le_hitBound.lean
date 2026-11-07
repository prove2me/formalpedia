-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.exactNeighborhood_eventMass_le_hitBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:03:13.594199+00:00
-- url     : https://prove2.me/submissions/d679dde6-ca6e-4e7f-87d9-2c893d7235c7

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_one_sub_coe_one_sub_pow_le
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_exactNeighborhood_eventMass

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (T : Finset (Fin (4 * r))) :
    eventMass
        (distribution r Delta hDelta)
        (fun sample => checkSetNeighborhood sample S = T) ≤
      ((S.card : ENNReal) *
        (incidenceProbability (4 * r) Delta : ENNReal)) ^ T.card *
      (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
        S.card) ^ (4 * r - T.card) := by
  rw [exactNeighborhood_eventMass r Delta hDelta S T]
  gcongr
  exact one_sub_coe_one_sub_pow_le
    (incidenceProbability (4 * r) Delta)
    (incidenceProbability_le_one hDelta)
    S.card
end QEC.Coding.FiberBundle.RandomBase
