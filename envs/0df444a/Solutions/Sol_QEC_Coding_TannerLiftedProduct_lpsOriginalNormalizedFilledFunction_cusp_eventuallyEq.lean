-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:30:25.830653+00:00
-- url     : https://prove2.me/submissions/96f2bb0d-8dde-43fc-ae57-ae54c4bc29d7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspPullback_eventuallyEq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_chart_eventually
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCuspChart_cusp
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (ρ : SL(2,ℤ))
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    (fun τ : ℍ => lpsOriginalNormalizedFilledFunction N hN F
      (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧))
      =ᶠ[UpperHalfPlane.atImInfty]
    (fun τ : ℍ => F (Sum.inl ⟦Matrix.SpecialLinearGroup.mapGL ℝ ρ • τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply lpsOriginalCuspPullback_eventuallyEq
  let x : LPSOriginalFilledCurve N := Sum.inr (lpsOriginalCuspOrbit N ρ)
  have hx : chartAt ℂ x x = (0 : ℂ) :=
    lpsOriginalFilledCuspChart_cusp N (lpsOriginalCuspOrbit N ρ)
  have hz : (0 : ℂ) ∈ (chartAt ℂ x).target := hx ▸ mem_chart_target ℂ x
  exact ((chartNormalizedMeromorphicFunction_chart_eventually F hF x 0 hz).filter_mono nhdsWithin_le_nhds).trans
    (MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (hF x) hz)
end QEC.Coding.TannerLiftedProduct
