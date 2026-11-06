-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.MeromorphicGerms.complexChartTransition_analytic_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:15.031312+00:00
-- url     : https://prove2.me/submissions/e84f75f7-d406-43bf-b0e3-119fa1b3cf69

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M]
namespace QEC.Coding.AlgebraicGeometry.MeromorphicGerms
theorem _root_.solution
    (x y : M) (z : ℂ)
    (hz : z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    AnalyticAt ℂ g z ∧ deriv g z ≠ 0 := by
  let e := chartAt ℂ x
  let d := chartAt ℂ y
  let g := e.symm.trans d
  have hc : ContDiffOn ℂ ω g g.source := by
    simpa only [g, e, d, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_target, extChartAt_coe, extChartAt_coe_symm, ext_coord_change_source,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.image_id,
      Function.id_comp, Function.comp_id] using
      (contDiffOn_ext_coord_change (I := 𝓘(ℂ)) y x)
  have hg : AnalyticAt ℂ g z :=
    (hc.contDiffAt (g.open_source.mem_nhds hz)).analyticAt
  have hi : ContDiffOn ℂ ω g.symm g.target := by
    simpa only [g, e, d, OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_target, extChartAt_coe, extChartAt_coe_symm, ext_coord_change_source,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.image_id,
      Function.id_comp, Function.comp_id] using
      (contDiffOn_ext_coord_change (I := 𝓘(ℂ)) x y)
  have hgi : AnalyticAt ℂ g.symm (g z) :=
    (hi.contDiffAt (g.open_target.mem_nhds (g.map_source hz))).analyticAt
  have he : (g.symm ∘ g) =ᶠ[𝓝 z] (fun t : ℂ => t) := by
    filter_upwards [g.open_source.mem_nhds hz] with t ht
    exact g.left_inv ht
  have hidentity : deriv (g.symm ∘ g) z = (1 : ℂ) := by
    rw [he.deriv_eq]
    exact deriv_id z
  have hchain := deriv_comp z hgi.differentiableAt hg.differentiableAt
  refine ⟨hg, ?_⟩
  intro hzero
  rw [hchain, hzero, mul_zero] at hidentity
  exact zero_ne_one hidentity
end QEC.Coding.AlgebraicGeometry.MeromorphicGerms
