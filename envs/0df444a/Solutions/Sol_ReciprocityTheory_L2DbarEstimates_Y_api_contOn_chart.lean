-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.api_contOn_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:31.007084+00:00
-- url     : https://prove2.me/submissions/fcb6367d-71c5-485e-ab30-5720837462ce

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeW
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {E : Type*} [TopologicalSpace E] (A : WeightedAtlas n Y ι La)
    (φ : Y → E) {U : Set Y} (hU : IsOpen U)
    (h : ∀ i, ContinuousOn (φ ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) :
    ContinuousOn φ U := by
  intro x hx
  set e := A.chart (A.pick x) with he
  have hxs : x ∈ e.source := A.mem_pick x
  have hex : e x ∈ e.target := e.map_source hxs
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hex, ?_⟩
    show e.symm (e x) ∈ U
    rw [e.left_inv hxs]
    exact hx
  have h1 : ContinuousAt (φ ∘ e.symm) (e x) :=
    (h (A.pick x)).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((φ ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hxs)
  have h3 : (φ ∘ e.symm) ∘ e =ᶠ[𝓝 x] φ := by
    filter_upwards [e.eventually_left_inverse hxs] with y hy
    simp [hy]
  exact (h2.congr h3).continuousWithinAt
end ReciprocityTheory.L2DbarEstimates.Y
