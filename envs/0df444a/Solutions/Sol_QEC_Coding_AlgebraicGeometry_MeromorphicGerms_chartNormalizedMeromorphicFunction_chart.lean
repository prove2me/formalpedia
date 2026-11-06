-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.chartNormalizedMeromorphicFunction_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:34.279531+00:00
-- url     : https://prove2.me/submissions/96773586-4699-417c-af26-3de8bea6de6a

import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_comp
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_eventuallyEq
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_on

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
    chartNormalizedMeromorphicFunction F ((chartAt ℂ x).symm z) =
      toMeromorphicNFOn (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x).target z := by
  let e := chartAt ℂ x
  let y := e.symm z
  let d := chartAt ℂ y
  let w := d y
  let g := d.symm.trans e
  have hys : y ∈ e.source := e.map_target hz
  have hyd : y ∈ d.source := mem_chart_source ℂ y
  have hw : w ∈ g.source := by
    change w ∈ d.target ∧ d.symm w ∈ e.source
    constructor
    · exact d.map_source hyd
    · change d.symm (d y) ∈ e.source
      rw [d.left_inv hyd]
      exact hys
  have hgz : g w = z := by
    change e (d.symm (d y)) = z
    rw [d.left_inv hyd]
    exact e.right_inv hz
  have ht : Tendsto g (𝓝[≠] w) (𝓝[≠] (g w)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(g.continuousAt hw).tendsto.mono_left nhdsWithin_le_nhds,
      g.eventually_ne_nhdsWithin hw⟩
  have hc : ContDiffOn ℂ ω (e ∘ d.symm) g.source := by
    simpa only [extChartAt_coe,extChartAt_coe_symm,ext_coord_change_source,
      modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Set.image_id,Function.id_comp,Function.comp_id] using (contDiffOn_ext_coord_change (I := 𝓘(ℂ)) x y)
  have hg : AnalyticAt ℂ (e ∘ d.symm) w :=
    (hc.contDiffAt (g.open_source.mem_nhds hw)).analyticAt
  have he : (F ∘ d.symm) =ᶠ[𝓝[≠] w] ((F ∘ e.symm) ∘ (e ∘ d.symm)) := by
    have hh : ∀ᶠ u in 𝓝[≠] w, u ∈ g.source := nhdsWithin_le_nhds (g.open_source.mem_nhds hw)
    filter_upwards [hh] with u hu
    have hu' : d.symm u ∈ e.source := hu.2
    simp only [Function.comp_def]
    rw [e.left_inv hu']
  change toMeromorphicNFAt (F ∘ d.symm) w w = _
  rw [normalizedGermValue_eventuallyEq _ _ w he]
  have hf : MeromorphicAt (F ∘ e.symm) ((e ∘ d.symm) w) := by
    change MeromorphicAt (F ∘ e.symm) (g w)
    rw [hgz]
    exact hF x z hz
  rw [normalizedGermValue_comp _ _ w hf hg ht]
  change toMeromorphicNFAt (F ∘ e.symm) (g w) (g w) = _
  rw [hgz]
  exact (normalizedGermValue_on _ _ z (hF x) hz).symm
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
