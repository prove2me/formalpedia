-- Prove2me | solution 2 for QEC.Coding.f256SelectedCoordinates_card_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:56:19.400841+00:00
-- url     : https://prove2.me/submissions/c0eb3150-1caf-453b-9828-03698a1bb8c5

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Theorems.Thm_QEC_Coding_f256SelectedCoordinates_card_pos

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : 1 ≤ f256SelectedCoordinates.card :=
  Nat.succ_le_iff.mpr f256SelectedCoordinates_card_pos
end QEC.Coding
