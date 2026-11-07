-- Prove2me | solution 2 for QEC.Coding.f256SelectedCoordinateFraction_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:37.279594+00:00
-- url     : https://prove2.me/submissions/d81bc555-7210-484f-b31b-3dcdffbdc5e1

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Theorems.Thm_QEC_Coding_f256SelectedCoordinates_card_ge_one

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    (1 : ℚ) / 512 ≤ f256SelectedCoordinateFraction := by
  rw [f256SelectedCoordinateFraction]
  have hcard : (1 : ℚ) ≤ f256SelectedCoordinates.card := by
    exact_mod_cast f256SelectedCoordinates_card_ge_one
  nlinarith
end QEC.Coding
