-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_analyticAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:24:06.363075+00:00
-- url     : https://prove2.me/submissions/feb3ce3a-6ed6-4e0e-bd71-a11a0866fe3f

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
    (x : M) (z : ℂ) (hz : z ∈ (chartAt ℂ x).target)
    (ho : 0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ x).symm) z) :
    AnalyticAt ℂ (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) z := by
  have ha := ((hF x z hz).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp ho
  have he := (chartNormalizedMeromorphicFunction_chart_eventually F hF x z hz).trans
    (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds (hF x) hz)
  exact ha.congr he.symm
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
