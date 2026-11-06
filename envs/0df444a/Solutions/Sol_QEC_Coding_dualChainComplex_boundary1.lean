-- Prove2me | solution 1 for QEC.Coding.dualChainComplex_boundary1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:03:27.599802+00:00
-- url     : https://prove2.me/submissions/d534f6d6-1a6a-4f2b-82d1-7a141503bb0f

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality

set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]
namespace QEC.Coding
theorem _root_.solution
    (K : ChainComplexData F
      (Word F i0) (Word F i1) (Word F i2)) :
    (dualChainComplex K).boundary1 =
      wordLinearMapTranspose K.boundary2 := rfl
end QEC.Coding
