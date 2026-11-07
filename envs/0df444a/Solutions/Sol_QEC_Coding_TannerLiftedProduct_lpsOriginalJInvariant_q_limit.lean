-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJInvariant_q_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:55.390879+00:00
-- url     : https://prove2.me/submissions/7df52e86-fe13-4902-bdf7-ce4bd7e862ed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQCoefficient_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_qParam_pullback

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Tendsto (fun τ : ℍ => Function.Periodic.qParam 1 (τ:ℂ)*lpsOriginalJInvariant τ)
      UpperHalfPlane.atImInfty (𝓝 1) := by
  have h := lpsOriginalJQCoefficient_analytic_zero.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  rw [lpsOriginalJQCoefficient_zero] at h
  exact h.congr (fun τ => (lpsOriginalJInvariant_qParam_pullback τ).symm)
end QEC.Coding.TannerLiftedProduct
