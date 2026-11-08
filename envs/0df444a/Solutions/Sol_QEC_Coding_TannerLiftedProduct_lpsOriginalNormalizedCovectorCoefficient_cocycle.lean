-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedCovectorCoefficient_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:30:34.270937+00:00
-- url     : https://prove2.me/submissions/5c144e5f-981e-48f8-b21c-6b3b4e875bfb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_complexChartTransition_analytic_unit
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_comp_mul_analyticUnit
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_eventuallyEq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledCovectorChartCoefficient_cocycle
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


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
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x) z z =
      toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma y)
        (g z) (g z) * deriv g z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
  let fx := lpsOriginalFilledCovectorChartCoefficient N hN sigma x
  let fy := lpsOriginalFilledCovectorChartCoefficient N hN sigma y
  have ha := complexChartTransition_analytic_unit x y z hz
  have hf : MeromorphicAt fy (g z) := hmer y (g z) ((g.map_source hz).1)
  have ht : Tendsto g (𝓝[≠] z) (𝓝[≠] (g z)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(g.continuousAt hz).tendsto.mono_left nhdsWithin_le_nhds,
        g.eventually_ne_nhdsWithin hz⟩
  have he : fx =ᶠ[𝓝[≠] z] ((fy ∘ g) * deriv g) := by
    filter_upwards [nhdsWithin_le_nhds (g.open_source.mem_nhds hz)] with w hw
    exact lpsOriginalFilledCovectorChartCoefficient_cocycle N hN sigma x y w hw
  change toMeromorphicNFAt fx z z = toMeromorphicNFAt fy (g z) (g z) * deriv g z
  rw [normalizedGermValue_eventuallyEq fx ((fy ∘ g) * deriv g) z he]
  exact normalizedGermValue_comp_mul_analyticUnit fy g (deriv g) z hf
    ha.1 ha.1.deriv ha.2 ht
end QEC.Coding.TannerLiftedProduct
