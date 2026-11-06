-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_meromorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:23:56.751945+00:00
-- url     : https://prove2.me/submissions/dbb6426f-f65c-48f5-9ea3-34221939a04f

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
    (x : M) :
    MeromorphicOn (chartNormalizedMeromorphicFunction F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target := by
  intro z hz
  exact (meromorphicNFOn_toMeromorphicNFOn _ _ hz).meromorphicAt.congr
    ((chartNormalizedMeromorphicFunction_chart_eventually F hF x z hz).symm.filter_mono nhdsWithin_le_nhds)
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
