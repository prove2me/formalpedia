-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.transpose_wordEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:05:19.234261+00:00
-- url     : https://prove2.me/submissions/d64ac742-a7b3-4a42-83e1-1ea0b9ea62a5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Regions
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) : wordLinearMapTranspose (wordEquiv e).symm.toLinearMap =
      (wordEquiv e).toLinearMap := by
  exact transpose_wordEquiv e.symm
end QEC.Coding.BDL26RXDecoderAdapter
