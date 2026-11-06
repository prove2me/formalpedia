-- Prove2me | solution 1 for QEC.Coding.dualChainComplex_boundary2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:03:49.838284+00:00
-- url     : https://prove2.me/submissions/1a9e7f31-f51b-4c46-ad75-060003da435b

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
    (dualChainComplex K).boundary2 =
      wordLinearMapTranspose K.boundary1 := rfl
end QEC.Coding
