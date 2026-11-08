-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsWeightTwoSlashPetersson_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:00:31.301588+00:00
-- url     : https://prove2.me/submissions/324b1f6d-7c73-41c2-a282-212321e81ebc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHorocyclePoint_im
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHorocyclePoint_im
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    ∃C:ℝ,∀τ, ‖petersson 2 (f ∣[(2:ℤ)] A) g τ‖ ≤ C := by
  obtain ⟨Cf,hf⟩ := CuspFormClass.petersson_bounded_left 2 _ f f
  obtain ⟨Cg,hg⟩ := CuspFormClass.petersson_bounded_left 2 _ g g
  refine ⟨(Cf+Cg)/2,fun τ => ?_⟩
  have he : petersson 2 (f ∣[(2:ℤ)] A) (f ∣[(2:ℤ)] A) τ = petersson 2 f f (A • τ) := by
    have hA' : 0 < (A : Matrix (Fin 2) (Fin 2) ℝ).det := hA
    simpa [UpperHalfPlane.σ,hA'] using petersson_slash 2 f f A τ
  have hf' : ‖petersson 2 (f ∣[(2:ℤ)] A) (f ∣[(2:ℤ)] A) τ‖ ≤ Cf := by
    rw [he]
    exact hf _
  have hg' := hg τ
  have hnon := mul_nonneg (sq_nonneg (‖((f:ℍ→ℂ) ∣[(2:ℤ)] A) τ‖-‖g τ‖)) (sq_nonneg τ.im)
  simp only [petersson,norm_mul,Complex.norm_conj,norm_zpow,Complex.norm_real,
    Real.norm_of_nonneg τ.im_pos.le] at hf' hg' ⊢
  norm_num only [Int.reduceNeg,Int.ofNat_eq_natCast, zpow_ofNat] at hf' hg' ⊢
  nlinarith
end QEC.Coding.TannerLiftedProduct
