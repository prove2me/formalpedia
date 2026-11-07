-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEisensteinDilation_weightedCuspGcd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:26:17.481189+00:00
-- url     : https://prove2.me/submissions/bdf5add5-109e-40d8-bb52-e111005441ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspGcd
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
theorem _root_.solution (N m : ℕ) (hm : 0<m)
    (γ : SL(2,ℤ)) (w : Fin N→ℂ) :
    (∑ r : Fin N,w r*((Int.gcd ((N:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
      ((N:ℤ)*γ 1 0):ℂ)^2/((N:ℂ)^2*(m:ℂ)^2)))=
      ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (∑ r : Fin N,w r*((Int.gcd ((N:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
          (r.val:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0)
          ((N:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0):ℂ)^2/(N:ℂ)^2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [lpsEisensteinDilationCuspGcd N r.val m hm γ]
  simp only [Nat.cast_mul]
  ring
end QEC.Coding.TannerLiftedProduct
