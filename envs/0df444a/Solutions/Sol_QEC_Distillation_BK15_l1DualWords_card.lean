-- Prove2me | solution 1 for QEC.Distillation.BK15.l1DualWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:16.181046+00:00
-- url     : https://prove2.me/submissions/bf47f69b-bee1-4270-bc03-8cffde9608a3

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1DualCoefficientMap_injective

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : l1DualWords.card = 2048 := by
  rw [l1DualWords, Finset.card_image_of_injective _ l1DualCoefficientMap_injective]
  decide +kernel
end QEC.Distillation.BK15
