-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_weaklyLocallyCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:13:43.201948+00:00
-- url     : https://prove2.me/submissions/873188d7-fe37-4d4b-8c30-ffce75ac18a2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) : WeaklyLocallyCompactSpace M := by
  refine ⟨fun x => ?_⟩
  obtain ⟨e, hx, -⟩ := hz x
  have ht : e x ∈ e.target := e.map_source hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) ht
  refine ⟨e.symm '' Metric.closedBall (e x) (r / 2), ?_, ?_⟩
  · exact (isCompact_closedBall _ _).image_of_continuousOn
      (e.continuousOn_symm.mono ((Metric.closedBall_subset_ball (by linarith)).trans hsub))
  · have h1 : e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2) ∈ 𝓝 x :=
      (e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds ⟨hx, Metric.mem_ball_self (by linarith)⟩
    refine Filter.mem_of_superset h1 ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨e y, Metric.ball_subset_closedBall hy2, e.left_inv hy1⟩
end ReciprocityTheory.L2DbarEstimates.F
