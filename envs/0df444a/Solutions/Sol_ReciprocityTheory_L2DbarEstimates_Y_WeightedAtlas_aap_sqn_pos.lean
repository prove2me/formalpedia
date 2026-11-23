-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.aap_sqn_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:58.542206+00:00
-- url     : https://prove2.me/submissions/3b0c864c-3554-4a5d-90b2-9c054f3c4e73

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (y : Y) : 0 < A.sqn L w y := by
  obtain ⟨k, hk⟩ := hD.no_common_zero y
  refine Finset.sum_pos' (fun j _ => by unfold nsq; positivity) ⟨k, Finset.mem_univ _, ?_⟩
  unfold nsq; have := norm_pos_iff.2 hk; positivity
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
