-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_weighted_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:39.952081+00:00
-- url     : https://prove2.me/submissions/64bfdb2b-f904-476d-9997-dad90b021240

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_of_dvd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (r : Fin q) :
    lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)=
      lpsQuadraticE2Character q (r.val:ZMod q)*
        (if (γ 0 0:ZMod q)+(r.val:ZMod q)*(D:ZMod q)=0 then (q:ℂ)^2 else 1) := by
  by_cases hr : r=0
  · subst r
    simp only [Fin.val_zero,Nat.cast_zero,MulChar.map_zero,zero_mul]
  · rw [lpsQuadraticEisensteinCuspGcd_of_dvd q γ r hr D hC]
    have he : (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=
        (γ 0 0:ZMod q)+(r.val:ZMod q)*(D:ZMod q) := by push_cast;rfl
    rw [he]
    have hq : (q:ℂ)≠0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    split_ifs
    · simp only [Nat.cast_pow]
      field_simp
    · simp [hq]
end QEC.Coding.TannerLiftedProduct
