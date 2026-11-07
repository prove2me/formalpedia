-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.signedEuler_jacobiBilateral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:57:20.846815+00:00
-- url     : https://prove2.me/submissions/075a405f-0a1d-46a1-99ec-8fbcfe626855

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_signedTriangularTerm_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_jacobiSignedCubeSeries_eq_tsum_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_hasSum_signedEuler_jtpPairs

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    signedEuler jacobiBilateral = -jacobiSignedCubeSeries := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  have hnonneg := summable_signedTriangularTerm_nonnegative
  have hseries : HasSum (fun t : ℕ =>
      -signedTriangularTerm (t : ℤ)) (-jacobiSignedCubeSeries) := by
    rw [jacobiSignedCubeSeries_eq_tsum_nonnegative]
    exact hnonneg.hasSum.neg
  exact (HasSum.congr_fun hasSum_signedEuler_jtpPairs
    (fun t => (signedEuler_jtpPair t).symm)).unique hseries
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
