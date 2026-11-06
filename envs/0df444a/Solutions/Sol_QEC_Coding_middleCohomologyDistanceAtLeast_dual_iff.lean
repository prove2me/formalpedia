-- Prove2me | solution 1 for QEC.Coding.middleCohomologyDistanceAtLeast_dual_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:24.774737+00:00
-- url     : https://prove2.me/submissions/3af6afe5-e5e7-46ec-b385-39f59cf47322

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Theorems.Thm_QEC_Coding_middleHomologyDistanceAtLeast_dual_iff
import Theorems.Thm_QEC_Coding_dualChainComplex_dual

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
    MiddleCohomologyDistanceAtLeast (dualChainComplex K) d ↔
      MiddleHomologyDistanceAtLeast K d := by
  rw [← middleHomologyDistanceAtLeast_dual_iff
    (dualChainComplex K) d]
  rw [dualChainComplex_dual]
end QEC.Coding
