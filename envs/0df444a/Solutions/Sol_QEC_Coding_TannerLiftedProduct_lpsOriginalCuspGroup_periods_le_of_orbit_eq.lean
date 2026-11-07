-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspGroup_periods_le_of_orbit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:41:03.114914+00:00
-- url     : https://prove2.me/submissions/2b93a73d-29de-47ea-9573-66ed632af957

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_conjugate_period
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspChange_translation
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
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ ρ' : SL(2, ℤ)) (h : lpsOriginalCuspOrbit N ρ = lpsOriginalCuspOrbit N ρ') :
    (lpsOriginalCuspGroup N ρ').strictPeriods ≤ (lpsOriginalCuspGroup N ρ).strictPeriods := by
  obtain ⟨g, hg, x, hx⟩ := lpsOriginalCuspChange_translation N ρ ρ' h
  let r := Matrix.SpecialLinearGroup.mapGL ℝ ρ
  let e := Matrix.SpecialLinearGroup.mapGL ℝ ρ'
  let d := r⁻¹ * g * e
  intro t ht
  have hp := Subgroup.mem_strictPeriods_iff.mp ht
  apply Subgroup.mem_strictPeriods_iff.mpr
  rw [lpsOriginalCuspGroup, ConjAct.toConjAct_inv,
    Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul] at hp ⊢
  change e * Matrix.GeneralLinearGroup.upperRightHom t * e⁻¹ ∈
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) at hp
  change r * Matrix.GeneralLinearGroup.upperRightHom t * r⁻¹ ∈
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))
  have he : r * Matrix.GeneralLinearGroup.upperRightHom t * r⁻¹ =
      g * (e * Matrix.GeneralLinearGroup.upperRightHom t * e⁻¹) * g⁻¹ := by
    calc
      _ = r * (d * Matrix.GeneralLinearGroup.upperRightHom t * d⁻¹) * r⁻¹ := by
        rw [lpsSignedTranslation_conjugate_period d x t hx]
      _ = _ := by
        dsimp only [d]
        simp only [mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hp) (Subgroup.inv_mem _ hg)
end QEC.Coding.TannerLiftedProduct
