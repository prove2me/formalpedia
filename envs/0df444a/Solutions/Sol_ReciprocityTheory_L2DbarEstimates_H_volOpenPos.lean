-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.volOpenPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:06:06.322089+00:00
-- url     : https://prove2.me/submissions/3fff254b-eb19-4c99-812c-c63dbcbbf5f0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_WeightedIntegralEqLintegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    VolOpenPosStatement n M := by
  intro z hz U hU ⟨x, hx⟩
  obtain ⟨e, he, hxe⟩ := exists_chart n z hz x
  have hW : IsOpen (U ∩ e.source) := hU.inter e.open_source
  have hinj : Set.InjOn z e.source := by
    intro a ha b hb hab
    rw [he ha, he hb] at hab
    exact e.injOn ha hb hab
  have himg : z '' (U ∩ e.source) = e '' (U ∩ e.source) :=
    Set.image_congr fun y hy => he hy.2
  have hpos : 0 < volume (z '' (U ∩ e.source)) := by
    rw [himg]
    exact (e.isOpen_image_of_subset_source hW Set.inter_subset_right).measure_pos _
      ⟨e x, x, ⟨hx, hxe⟩, rfl⟩
  rw [← vol_image n z hz e.source e.open_source hinj _ hW.measurableSet
    Set.inter_subset_right] at hpos
  exact hpos.trans_le (measure_mono Set.inter_subset_left)
end ReciprocityTheory.L2DbarEstimates.H
