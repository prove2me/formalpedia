-- Prove2me | solution 1 for QEC.Distillation.BK15.l1LogicalCosetWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:10:09.534646+00:00
-- url     : https://prove2.me/submissions/39422a7a-7411-4b39-a67d-1ca075334965

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l1Words_card

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : l1LogicalCosetWords.card = 16 := by
  rw [l1LogicalCosetWords,
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), l1Words_card]
end QEC.Distillation.BK15
