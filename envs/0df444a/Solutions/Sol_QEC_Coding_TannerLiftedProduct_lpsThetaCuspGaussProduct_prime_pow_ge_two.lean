-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_prime_pow_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:39:34.278467+00:00
-- url     : https://prove2.me/submissions/fbb13993-772f-4ca0-86fa-7a8aeb31d9bc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_unit_square
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_prime_pow_fourth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_odd_square_scale


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (e : ℕ) (a : ℤ) (ha : IsUnit (a:ZMod (q^(e+2)))) :
    lpsThetaCuspGaussProduct q a (q^(e+2))=(q:ℂ)^3*((q^(e+2):ℕ):ℂ)^2 := by
  have hodd : Odd (q^(e+2)) := ((Fact.out : q.Prime).odd_of_ne_two hq2).pow
  have h2 : IsUnit (2:ZMod (q^(e+2))) :=
    (ZMod.isUnit_iff_coprime 2 _).mpr hodd.coprime_two_left
  have hN : q^(e+2)=q^2*q^e := by rw [pow_add];ring
  have hs := lpsUnaryQuadraticGauss_odd_square_scale (q^(e+2)) q (q^e) hN
    (Fact.out : q.Prime).pos (pow_pos (Fact.out : q.Prime).pos _) a ha h2
  have he : 4*(q:ℤ)^2*a=(a*(q:ℤ)^2)*(2:ℤ)^2 := by ring
  rw [lpsThetaCuspGaussProduct,he,lpsUnaryQuadraticGauss_unit_square _ (a*(q:ℤ)^2) 2 (by exact_mod_cast h2),hs]
  rw [show lpsUnaryQuadraticGauss a (q^(e+2))*((q:ℂ)*lpsUnaryQuadraticGauss a (q^(e+2)))^3=
      (q:ℂ)^3*lpsUnaryQuadraticGauss a (q^(e+2))^4 by ring]
  rw [lpsUnaryQuadraticGauss_odd_prime_pow_fourth q (Fact.out : q.Prime) hq2 (e+2) a ha]
end QEC.Coding.TannerLiftedProduct
