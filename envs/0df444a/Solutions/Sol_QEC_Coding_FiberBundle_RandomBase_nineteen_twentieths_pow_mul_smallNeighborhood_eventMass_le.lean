-- Prove2me | solution 1 for QEC.Coding.FiberBundle.RandomBase.nineteen_twentieths_pow_mul_smallNeighborhood_eventMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:13:35.031966+00:00
-- url     : https://prove2.me/submissions/69b96f71-7889-4a7d-a7cd-8ebcd516b185

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_nineteen_twentieths_generatorBase_le_of_small
import Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weight_pow_mul_smallNeighborhood_eventMass_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory
namespace QEC.Coding.FiberBundle.RandomBase
theorem _root_.solution
    (r Delta : Nat) (hr : 0 < r) (hDelta : Delta ≤ 4 * r)
    (S : Finset (Fin (3 * r)))
    (hSmall : 100000 * Delta * S.card ≤ 3 * r)
    (cutoff : Nat) :
    ((19 : ENNReal) / 20) ^ cutoff *
        eventMass
          (distribution r Delta hDelta)
          (fun sample =>
            (checkSetNeighborhood sample S).card ≤ cutoff) ≤
      (((1 -
          (1 : NNReal) / 20 *
            ((399997 : NNReal) / 400000 *
              ((S.card : NNReal) *
                incidenceProbability (4 * r) Delta)) : NNReal) :
        ENNReal) ^ (4 * r)) := by
  calc
    _ ≤ (((19 : ENNReal) / 20) *
          (1 -
            (((1 - incidenceProbability (4 * r) Delta : NNReal) :
              ENNReal) ^ S.card)) +
        (((1 - incidenceProbability (4 * r) Delta : NNReal) : ENNReal) ^
          S.card)) ^ (4 * r) := by
      have hWeightNN : (19 : NNReal) / 20 ≤ 1 := by
        apply div_le_one_of_le₀
        · norm_num
        · exact bot_le
      have hWeightEq :
          (((19 : NNReal) / 20 : NNReal) : ENNReal) =
            (19 : ENNReal) / 20 :=
        ENNReal.coe_div (by norm_num)
      have hWeight : (19 : ENNReal) / 20 ≤ 1 := by
        rw [← hWeightEq]
        exact_mod_cast hWeightNN
      exact weight_pow_mul_smallNeighborhood_eventMass_le
        r Delta hDelta S cutoff ((19 : ENNReal) / 20) hWeight
    _ ≤ _ := by
      apply pow_le_pow_left'
      have hWeightEq :
          (((19 : NNReal) / 20 : NNReal) : ENNReal) =
            (19 : ENNReal) / 20 :=
        ENNReal.coe_div (by norm_num)
      rw [← hWeightEq]
      rw [← ENNReal.coe_pow]
      rw [← ENNReal.coe_one]
      rw [← ENNReal.coe_sub]
      exact_mod_cast nineteen_twentieths_generatorBase_le_of_small
        r Delta hr hDelta S hSmall
end QEC.Coding.FiberBundle.RandomBase
