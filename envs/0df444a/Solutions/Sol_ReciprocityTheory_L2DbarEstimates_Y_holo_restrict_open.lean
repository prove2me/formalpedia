-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.holo_restrict_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:37.635345+00:00
-- url     : https://prove2.me/submissions/18f94437-d030-4dae-9726-fa565977f9e6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DifferentiableAtLocalCoordinates
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n) (u : M → ℂ)
    (hu : Holo n z u) (S : Set M) (hS : IsOpen S) [Nonempty S] :
    Holo n (fun x : S => z x) (fun x : S => u x) := by
  intro e he
  let f := hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : S → M)
  have hc : IsChart n z (f.symm.trans e) := by
    intro x hx
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, f, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hx
    obtain ⟨⟨x', rfl⟩, hx2⟩ := hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, f,
      hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv] at hx2 ⊢
    exact he hx2
  have h2 := hu _ hc
  have ht : (f.symm.trans e).target = e.target := by
    simp [f]
  rw [ht] at h2
  refine h2.congr (fun v hv => ?_)
  simp [f, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
end ReciprocityTheory.L2DbarEstimates.Y
