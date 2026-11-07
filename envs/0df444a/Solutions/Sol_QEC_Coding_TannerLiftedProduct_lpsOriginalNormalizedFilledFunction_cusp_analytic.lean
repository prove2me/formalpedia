-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_cusp_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:18:25.297636+00:00
-- url     : https://prove2.me/submissions/b89cd368-bf2c-485d-8c91-fe1ee4f75ba2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspNormalization
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_analyticAt
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
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hc : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ c, 0 ≤ meromorphicOrderAt
        (F ∘ (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inr c : LPSOriginalFilledCurve N) (Sum.inr c)))
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ (fun q => lpsOriginalNormalizedFilledFunction N hN F
      ((lpsOriginalFilledCuspChart N c).symm q)) 0 := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let x : LPSOriginalFilledCurve N := Sum.inr c
  have hx : chartAt ℂ x x = (0 : ℂ) := lpsOriginalFilledCuspChart_cusp N c
  have hz : (0 : ℂ) ∈ (chartAt ℂ x).target := hx ▸ mem_chart_target ℂ x
  have ho : 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) 0 := hx ▸ hc c
  exact chartNormalizedMeromorphicFunction_analyticAt F hF x 0 hz ho
end QEC.Coding.TannerLiftedProduct
