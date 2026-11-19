-- Prove2me | solution 1 for QEC.Distillation.BK15.l2DualWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:33.96778+00:00
-- url     : https://prove2.me/submissions/8b3e1ea7-25b3-4c0e-9495-1c8eac6b228d

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2DualCoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : l2DualWords.card = 32 := by
  rw [l2DualWords, Finset.card_image_of_injective _ l2DualCoefficientMap_injective]
  decide +kernel
end QEC.Distillation.BK15
