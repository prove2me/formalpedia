-- Prove2me | solution 1 for QEC.Coding.dual_middleBoundaryCode_carrier_eq_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:12.46693+00:00
-- url     : https://prove2.me/submissions/d7a7da13-afb6-4585-8193-29c51f61cde7

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
    (dualChainComplex K).middleBoundaryCode.carrier =
      K.firstCoboundaryCheckCode.carrier := rfl
end QEC.Coding
