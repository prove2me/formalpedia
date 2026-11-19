-- Prove2me | solution 1 for QEC.Distillation.BK15.l1Words_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:04:25.514807+00:00
-- url     : https://prove2.me/submissions/ffd05ca2-b937-46c8-a31f-621091d9cd29

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : l1Words.card = 16 := by
  rw [l1Words, Finset.card_image_of_injective _ l1CoefficientMap_injective]
  decide +kernel
end QEC.Distillation.BK15
