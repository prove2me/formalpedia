-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_stabilizer_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:32:03.535567+00:00
-- url     : https://prove2.me/submissions/4702acef-b646-45fc-97c2-359f68fbe1a6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCongruenceSturm
import Mathlib.NumberTheory.ModularForms.Cusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspWidths
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_neg_one_mem
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_periods_generated
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegralFixInfinity_translation
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (ρ : SL(2,ℤ))
    (g : GL (Fin 2) ℝ) (hg : g∈lpsOriginalCuspGroup N ρ)
    (hfix : g • (OnePoint.infty : OnePoint ℝ)=OnePoint.infty) :
    ∃ m : ℤ, g=Matrix.GeneralLinearGroup.upperRightHom
        (m • (lpsOriginalCuspGroup N ρ).strictWidthInfty) ∨
      g= -Matrix.GeneralLinearGroup.upperRightHom
        (m • (lpsOriginalCuspGroup N ρ).strictWidthInfty) := by
  obtain ⟨x,hx⟩ := lpsIntegralFixInfinity_translation g
    (lpsOriginalCuspGroup_le_SLRange N ρ hg) (OnePoint.smul_infty_eq_self_iff.mp hfix)
  have hp : x∈(lpsOriginalCuspGroup N ρ).strictPeriods := by
    apply Subgroup.mem_strictPeriods_iff.mpr
    rcases hx with he|he
    · rwa [←he]
    · have hneg := Subgroup.mul_mem (lpsOriginalCuspGroup N ρ)
        (lpsOriginalCuspGroup_neg_one_mem N ρ) hg
      simpa [he] using hneg
  rw [lpsOriginalCuspGroup_periods_generated] at hp
  obtain ⟨m,hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hp
  exact ⟨m,hm.symm ▸ hx⟩
end QEC.Coding.TannerLiftedProduct
