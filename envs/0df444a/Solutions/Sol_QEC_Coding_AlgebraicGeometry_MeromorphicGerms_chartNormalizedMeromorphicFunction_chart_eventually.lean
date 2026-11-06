-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_chart_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:59:30.66768+00:00
-- url     : https://prove2.me/submissions/d9cb2e7f-0672-4f1c-9a9c-3f1dc33980c9

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_chart

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
    (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) =ᶠ[𝓝 z]
      toMeromorphicNFOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := by
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds hz] with u hu
  exact chartNormalizedMeromorphicFunction_chart F hF x u hu
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
