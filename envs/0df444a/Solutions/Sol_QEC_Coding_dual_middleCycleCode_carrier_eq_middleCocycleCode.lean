-- Prove2me | solution 1 for QEC.Coding.dual_middleCycleCode_carrier_eq_middleCocycleCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:08.55456+00:00
-- url     : https://prove2.me/submissions/269a6b35-3b43-4bc6-ad3a-c20565cd08ef

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
    (dualChainComplex K).middleCycleCode.carrier =
      K.middleCocycleCode.carrier := rfl
end QEC.Coding
