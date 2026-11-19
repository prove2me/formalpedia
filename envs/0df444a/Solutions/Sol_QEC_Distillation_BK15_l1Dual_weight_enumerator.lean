-- Prove2me | solution 1 for QEC.Distillation.BK15.l1Dual_weight_enumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:11:30.747943+00:00
-- url     : https://prove2.me/submissions/1771bbcc-3470-42e6-af24-24bb98f650cc

import Definitions.Def_QECert_FifteenWeights_WeightAggregation
import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1DualCoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (weight : Fin 16) :
    weightCount l1DualWords weight.1 =
      if weight = 0 then 1 else if weight = 3 then 35 else
      if weight = 4 then 105 else if weight = 5 then 168 else
      if weight = 6 then 280 else if weight = 7 then 435 else
      if weight = 8 then 435 else if weight = 9 then 280 else
      if weight = 10 then 168 else if weight = 11 then 105 else
      if weight = 12 then 35 else if weight = 15 then 1 else 0 := by
  -- Count injective coefficient images without repeatedly deduplicating all words.
  rw [weightCount, l1DualWords, Finset.filter_image,
    Finset.card_image_of_injective _ l1DualCoefficientMap_injective]
  exact QEC.Distillation.BK15.CertifiedWeights.dual_coefficient_enumerator weight
end QEC.Distillation.BK15