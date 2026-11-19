-- Prove2me | solution 1 for QEC.Distillation.BK15.l1_weight_enumerator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:48.825276+00:00
-- url     : https://prove2.me/submissions/6c465c5b-4eba-4bde-be46-ea7aa37fb563

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution (weight : Fin 16) :
    weightCount l1Words weight.1 =
      if weight = 0 then 1 else if weight = 8 then 15 else 0 := by
  rw [weightCount, l1Words, Finset.filter_image,
    Finset.card_image_of_injective _ l1CoefficientMap_injective]
  revert weight
  decide +kernel
end QEC.Distillation.BK15
