-- Prove2me | solution 1 for QEC.Distillation.BK15.l2_weight_enumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:55.328729+00:00
-- url     : https://prove2.me/submissions/e1b2afbe-f3f7-4766-b81d-f68ad1724edd

import Definitions.Def_QECert_FifteenWeights_WeightAggregation
import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (weight : Fin 16) :
    weightCount l2Words weight.1 =
      if weight = 0 then 1 else if weight = 4 then 105 else
      if weight = 6 then 280 else if weight = 8 then 435 else
      if weight = 10 then 168 else if weight = 12 then 35 else 0 := by
  rw [weightCount, l2Words, Finset.filter_image,
    Finset.card_image_of_injective _ l2CoefficientMap_injective]
  exact QEC.Distillation.BK15.CertifiedWeights.coefficient_enumerator weight
end QEC.Distillation.BK15