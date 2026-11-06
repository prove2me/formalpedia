-- Prove2me | solution 1 for QEC.Coding.middleHomologyDistanceAtLeast_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:37:58.813777+00:00
-- url     : https://prove2.me/submissions/eca40bfb-1d81-4ddc-bb2f-64c47556bcec

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
      (Word F i0) (Word F i1) (Word F i2))
    (d : Nat) :
    MiddleHomologyDistanceAtLeast (dualChainComplex K) d ↔
      MiddleCohomologyDistanceAtLeast K d := by
  rfl
end QEC.Coding
