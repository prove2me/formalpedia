-- Prove2me | solution 1 for QEC.Coding.f256MFEFromSelfDual_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:54:41.276128+00:00
-- url     : https://prove2.me/submissions/5dd37d41-ccd4-4df6-9ae6-efab9968fe96

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Theorems.Thm_QEC_Coding_f256MFESigma_injective


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators
namespace QEC.Coding
theorem _root_.solution : Function.Injective f256MFEFromSelfDual :=
  f256MFESigma_injective.comp f256SelfDualBasis.equivFun.symm.injective
end QEC.Coding
