-- Prove2me | solution 2 for QEC.Coding.f256MFEpi3_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:39.411642+00:00
-- url     : https://prove2.me/submissions/cef4267b-03b9-4300-97b5-6c67852e706a

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Theorems.Thm_QEC_Coding_f256MFEpi2_apply

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution (i j k : Fin 8) :
    f256MFEpi3 (f256MFEIndex i j k) = f256MFEIndex k i j := by
  rw [f256MFEpi3, Equiv.trans_apply, f256MFEpi2_apply, f256MFEpi2_apply]
end QEC.Coding
