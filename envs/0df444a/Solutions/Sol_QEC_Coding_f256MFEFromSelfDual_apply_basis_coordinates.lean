-- Prove2me | solution 1 for QEC.Coding.f256MFEFromSelfDual_apply_basis_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:40.161225+00:00
-- url     : https://prove2.me/submissions/af686e8a-03a0-4aeb-8dd8-2432e6f89e92

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution (x : F256) :
    f256MFEFromSelfDual (f256SelfDualBasis.equivFun x) = f256MFESigma x := by
  simp [f256MFEFromSelfDual]
end QEC.Coding
