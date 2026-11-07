-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoordinate_analytic_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:50:18.713966+00:00
-- url     : https://prove2.me/submissions/1475e9e2-47e1-4541-b279-22d99be3ecd2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspDifferentialCharts
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_smul_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQParam_smul_deriv_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoordinate_eventually_mobius
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspGroup_width_positive


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (ρ : SL(2,ℤ)) (τ : ℍ)
    (hx : Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) ∈
        lpsOriginalFilledCuspSource N ρ) :
    let f : ℂ → ℂ := fun z => lpsOriginalFilledCuspPartialEquiv N ρ
        (Sum.inl (Quotient.mk (MulAction.orbitRel
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
          (UpperHalfPlane.ofComplex z)))
    AnalyticAt ℂ f (τ:ℂ) ∧ deriv f (τ:ℂ)≠0 := by
  obtain ⟨g,hd,he⟩ := lpsOriginalCuspCoordinate_eventually_mobius N ρ τ hx
  have hg : 0<g.val.det := by rw [hd];norm_num
  constructor
  · exact (lpsQParam_smul_analytic _ g hg τ).congr he.symm
  · rw [he.deriv_eq]
    exact lpsQParam_smul_deriv_ne_zero _
      (lpsOriginalCuspGroup_width_positive N ρ).ne' g hg τ
end QEC.Coding.TannerLiftedProduct
