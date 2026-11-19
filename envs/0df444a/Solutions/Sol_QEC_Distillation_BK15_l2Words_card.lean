-- Prove2me | solution 1 for QEC.Distillation.BK15.l2Words_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:04:40.268477+00:00
-- url     : https://prove2.me/submissions/6dc272dc-9471-4959-a6ca-7487429cd7b0

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2CoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : l2Words.card = 1024 := by
  rw [l2Words, Finset.card_image_of_injective _ l2CoefficientMap_injective]
  decide +kernel
end QEC.Distillation.BK15
