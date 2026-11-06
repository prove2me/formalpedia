-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_codiscrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:24:03.848012+00:00
-- url     : https://prove2.me/submissions/19e96695-5850-4c31-bd59-164e4d55e357

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
    (F : M → ℂ) (hF : ∀ x : M, MeromorphicOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target) :
    F =ᶠ[Filter.codiscrete M] chartNormalizedMeromorphicFunction F := by
  change {y | F y = chartNormalizedMeromorphicFunction F y} ∈ Filter.codiscreteWithin (Set.univ : Set M)
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  simp only [Set.compl_univ,Set.union_empty]
  let e := chartAt ℂ x
  have hs : x ∈ e.source := mem_chart_source ℂ x
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt hs).tendsto.mono_left nhdsWithin_le_nhds,
      e.eventually_ne_nhdsWithin hs⟩
  have hh := ht.eventually ((hF x).toMeromorphicNFOn_eq_self_on_nhdsNE (e.map_source hs))
  have hsrc : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source := nhdsWithin_le_nhds (e.open_source.mem_nhds hs)
  filter_upwards [hh,hsrc] with y hy hys
  have hc := chartNormalizedMeromorphicFunction_chart F hF x (e y) (e.map_source hys)
  rw [e.left_inv hys] at hc
  change toMeromorphicNFOn (F ∘ e.symm) e.target (e y) = F (e.symm (e y)) at hy
  rw [e.left_inv hys] at hy
  exact hy.symm.trans hc.symm
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
