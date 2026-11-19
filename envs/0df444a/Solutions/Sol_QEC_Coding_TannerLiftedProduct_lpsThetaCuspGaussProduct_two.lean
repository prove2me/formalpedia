-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:39:39.529962+00:00
-- url     : https://prove2.me/submissions/f347f332-d75c-446c-a2c6-43537d33c941

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_odd_of_even_modulus


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod 2)) :
    lpsThetaCuspGaussProduct q a 2=0 := by
  have ho := lpsZMod_unit_odd_of_even_modulus 2 (by decide) a ha
  rw [lpsThetaCuspGaussProduct,lpsUnaryQuadraticGauss_odd_two a ho,zero_mul]
end QEC.Coding.TannerLiftedProduct
