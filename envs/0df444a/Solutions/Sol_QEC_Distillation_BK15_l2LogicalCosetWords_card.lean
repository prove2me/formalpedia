-- Prove2me | solution 1 for QEC.Distillation.BK15.l2LogicalCosetWords_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T01:09:56.768017+00:00
-- url     : https://prove2.me/submissions/c2aadfeb-9735-4a3d-b0ef-a3313aa4a9ec

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Theorems.Thm_QEC_Distillation_BK15_l2Words_card

set_option autoImplicit false
open QEC QEC.Distillation QEC.Distillation.BK15
open QEC Coding
namespace QEC.Distillation.BK15
theorem _root_.solution : l2LogicalCosetWords.card = 1024 := by
  rw [l2LogicalCosetWords,
    Finset.card_image_of_injective _ (fun _ _ h => add_right_cancel h), l2Words_card]
end QEC.Distillation.BK15
