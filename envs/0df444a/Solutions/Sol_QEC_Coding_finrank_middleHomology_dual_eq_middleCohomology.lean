-- Prove2me | solution 1 for QEC.Coding.finrank_middleHomology_dual_eq_middleCohomology
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:49:14.988589+00:00
-- url     : https://prove2.me/submissions/31ae84e4-1217-4a22-9342-ae67e5050bf0

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
    Module.finrank F (dualChainComplex K).middleHomology =
      Module.finrank F K.middleCohomology := by
  rfl
end QEC.Coding
