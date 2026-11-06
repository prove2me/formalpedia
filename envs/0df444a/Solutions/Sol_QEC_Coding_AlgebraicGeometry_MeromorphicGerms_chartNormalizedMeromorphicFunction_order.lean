-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_order
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:24:00.830508+00:00
-- url     : https://prove2.me/submissions/6ed5eca0-4bb6-4c39-9a67-355b4c7d8c81

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_chart_eventually

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target)
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target) :
    meromorphicOrderAt (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) z =
      meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) z := by
  rw [meromorphicOrderAt_congr ((chartNormalizedMeromorphicFunction_chart_eventually F hF x z hz).filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_toMeromorphicNFOn (hF x) hz
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
