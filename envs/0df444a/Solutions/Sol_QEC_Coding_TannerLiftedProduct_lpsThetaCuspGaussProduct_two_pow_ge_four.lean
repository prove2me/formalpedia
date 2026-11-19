-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_two_pow_ge_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:08.001048+00:00
-- url     : https://prove2.me/submissions/b4fbe963-e7c0-4915-aff8-654051d6b0b1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_unit_square
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_square_scale
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_two_pow_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsZMod_unit_bezout


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (hq : Odd q)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (2^(e+4)))) :
    lpsThetaCuspGaussProduct q a (2^(e+4))= -32*((2^(e+4):ℕ):ℂ)^2 := by
  have hc : q.Coprime (2^(e+4)) := hq.coprime_two_right.pow_right _
  have hu : IsUnit ((q:ℤ):ZMod (2^(e+4))) := by
    exact_mod_cast (ZMod.isUnit_iff_coprime q (2^(e+4))).mpr hc
  have hN : 2^(e+4)=4*2^2*2^e := by rw [pow_add];ring
  obtain ⟨b,u,hd⟩ := lpsZMod_unit_bezout (2^(e+4)) a ha
  have hs := lpsUnaryQuadraticGauss_square_scale (2^(e+4)) 2 (2^e) hN
    (by decide) (by positivity) a b u hd
  norm_num only [Nat.cast_ofNat] at hs
  have he : 4*(q:ℤ)^2*a=(a*(2:ℤ)^2)*(q:ℤ)^2 := by ring
  rw [lpsThetaCuspGaussProduct,he,lpsUnaryQuadraticGauss_unit_square _ (a*(2:ℤ)^2) q hu]
  rw [show a*(2:ℤ)^2=a*4 by ring,hs]
  rw [show lpsUnaryQuadraticGauss a (2^(e+4))*((2:ℂ)*lpsUnaryQuadraticGauss a (2^(e+4)))^3=
      8*lpsUnaryQuadraticGauss a (2^(e+4))^4 by ring]
  have hf := lpsUnaryQuadraticGauss_two_pow_fourth (e+2) a ha
  rw [show e+2+2=e+4 by omega] at hf
  rw [hf]
  ring
end QEC.Coding.TannerLiftedProduct
