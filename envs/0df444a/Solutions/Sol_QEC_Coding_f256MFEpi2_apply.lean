-- Prove2me | solution 1 for QEC.Coding.f256MFEpi2_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:23:58.908183+00:00
-- url     : https://prove2.me/submissions/c907ebfd-c7ec-4fc2-9ed7-0a633164e2ba

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (i j k : Fin 8) :
    f256MFEpi2 (f256MFEIndex i j k) = f256MFEIndex j k i := by
  simp [f256MFEpi2, f256MFEIndex]
end QEC.Coding
