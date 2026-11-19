-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:03.097472+00:00
-- url     : https://prove2.me/submissions/48fcf3e2-e2a6-4e97-8b9f-fc14248cd1ca

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_inflate
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_odd_of_even_modulus


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : Odd q) (a : ℤ)
    (ha : IsUnit (a:ZMod 8)) : lpsThetaCuspGaussProduct q a 8=0 := by
  have ho := lpsZMod_unit_odd_of_even_modulus 8 (by decide) a ha
  have hqo : Odd ((q:ℤ)^2*a) := by
    exact (show Odd (q:ℤ) by exact_mod_cast hq).pow.mul ho
  have hz : lpsUnaryQuadraticGauss (4*(q:ℤ)^2*a) 8=0 := by
    have h := lpsUnaryQuadraticGauss_inflate 4 2 ((q:ℤ)^2*a)
    rw [lpsUnaryQuadraticGauss_odd_two _ hqo,mul_zero] at h
    have he : (q:ℤ)^2*a*(4:ℤ)=4*(q:ℤ)^2*a := by ring
    norm_num only [Nat.cast_ofNat] at h
    rw [show (q:ℤ)^2*a*4=4*(q:ℤ)^2*a by ring] at h
    exact h
  rw [lpsThetaCuspGaussProduct,hz,zero_pow (by decide : (3:ℕ)≠0),mul_zero]
end QEC.Coding.TannerLiftedProduct
