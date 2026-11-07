-- Prove2me | solution 2 for QEC.Coding.f256SelectorQ0_mem_selectedCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:53:23.360335+00:00
-- url     : https://prove2.me/submissions/4ed24d97-d620-4b9f-8b97-cf5d57159532

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Theorems.Thm_QEC_Coding_f256SelectorCoefficient_q0

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution :
    f256SelectorQ0 ∈ f256SelectedCoordinates := by
  simp [f256SelectedCoordinates, f256SelectorCoefficient_q0]
end QEC.Coding
