-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_contMDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:00:19.772809+00:00
-- url     : https://prove2.me/submissions/1d68e42e-f28d-40ee-bea0-9753da705ce7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_on
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_inCoordinates


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (horder : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : LPSOriginalFilledCurve N,
        0 ≤ meromorphicOrderAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
          (chartAt ℂ x x)) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : LPSOriginalFilledCurve N => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun y : LPSOriginalFilledCurve N =>
          TangentSpace 𝓘(ℂ) y →L[ℂ] Bundle.Trivial (LPSOriginalFilledCurve N) ℂ y)
        x (lpsOriginalNormalizedFilledCovector N hN sigma x)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro x
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  let e := chartAt ℂ x
  let f := lpsOriginalFilledCovectorChartCoefficient N hN sigma x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source ℂ x)
  have ha : AnalyticAt ℂ (toMeromorphicNFAt f (e x)) (e x) :=
    ((hmer x (e x) hx).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
      (horder x)
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e x :=
    contMDiffAt_extChartAt (I := 𝓘(ℂ))
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => toMeromorphicNFAt f (e x) (e y)) x :=
    ha.contDiffAt.contMDiffAt.comp x hc
  have hm := (ContinuousLinearMap.mul ℂ ℂ).contMDiffAt (n := ω) |>.comp x hg
  apply hm.congr_of_eventuallyEq
  have hf : toMeromorphicNFOn f e.target =ᶠ[𝓝 (e x)] toMeromorphicNFAt f (e x) :=
    toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hmer x) hx
  have hfixed := hc.continuousAt.tendsto.eventually hf
  filter_upwards [e.open_source.mem_nhds (mem_chart_source ℂ x), hfixed] with y hy hfy
  rw [lpsOriginalNormalizedFilledCovector_inCoordinates N hN sigma hmer x y hy]
  have hnorm := normalizedGermValue_on f e.target (e y) (hmer x) (e.map_source hy)
  rw [← hnorm, hfy]
  rfl
end QEC.Coding.TannerLiftedProduct
