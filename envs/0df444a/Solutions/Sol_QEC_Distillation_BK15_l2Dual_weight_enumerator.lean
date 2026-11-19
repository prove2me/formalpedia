-- Prove2me | solution 1 for QEC.Distillation.BK15.l2Dual_weight_enumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:11:44.751675+00:00
-- url     : https://prove2.me/submissions/d03fc245-383d-4c27-b3a6-d9f9c165fdb9

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2DualCoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (weight : Fin 16) :
    weightCount l2DualWords weight.1 =
      if weight = 0 then 1 else if weight = 7 then 15 else
      if weight = 8 then 15 else if weight = 15 then 1 else 0 := by
  rw [weightCount, l2DualWords, Finset.filter_image,
    Finset.card_image_of_injective _ l2DualCoefficientMap_injective]
  revert weight
  decide +kernel
end QEC.Distillation.BK15
