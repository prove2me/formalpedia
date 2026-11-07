-- Prove2me | solution 2 for QEC.Coding.f256MFESigma_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:48:41.69969+00:00
-- url     : https://prove2.me/submissions/abeb202d-18cc-40b8-b015-8c92ac1b5f71

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Theorems.Thm_QEC_Coding_f256MFESigma_apply

set_option autoImplicit false
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : Function.Injective f256MFESigma := by
  intro x y hxy
  apply f256PolynomialBasis.equivFun.injective
  ext i
  have hcoordinate := congr_fun hxy (f256MFEIndex i 0 0)
  simpa only [f256MFESigma_apply] using hcoordinate
end QEC.Coding
