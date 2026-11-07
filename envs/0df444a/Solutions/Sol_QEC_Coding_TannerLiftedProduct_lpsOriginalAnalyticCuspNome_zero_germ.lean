-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalAnalyticCuspNome_zero_germ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:42:10.846945+00:00
-- url     : https://prove2.me/submissions/e21af72d-307b-4367-9761-3635bfef4bac

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAnalyticCuspLocalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (F : lpsOriginalCuspAnalyticSubring)
    (hF : ∀ τ : ℍ,F.val (Function.Periodic.qParam 1 (τ:ℂ))=0) :
    F.val=ᶠ[𝓝 (0:ℂ)]0 := by
  have hDisk : ∀ q : ℂ, ‖q‖<1 → q≠0 → F.val q=0 := by
    intro q hq hq0
    let τ : ℍ := ⟨Function.Periodic.invQParam 1 q,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0⟩
    have hqτ : Function.Periodic.qParam 1 (τ:ℂ)=q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    simpa only [hqτ] using hF τ
  have hsmall : ∀ᶠ q : ℂ in 𝓝 0, ‖q‖<1 :=
    (isOpen_lt (continuous_norm : Continuous (fun q : ℂ=>‖q‖)) continuous_const).mem_nhds
      (by norm_num : ‖(0:ℂ)‖<1)
  have hp : F.val=ᶠ[𝓝[≠] (0:ℂ)]0 := by
    filter_upwards [hsmall.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with q hq hq0
    exact hDisk q hq hq0
  have h0 : F.val 0=0 := tendsto_nhds_unique_of_eventuallyEq
    (F.property.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hp
  filter_upwards [hsmall] with q hq
  by_cases hq0 : q=0
  · subst q;exact h0
  · exact hDisk q hq hq0
end QEC.Coding.TannerLiftedProduct
