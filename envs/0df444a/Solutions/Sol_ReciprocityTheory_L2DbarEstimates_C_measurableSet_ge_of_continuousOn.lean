-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.measurableSet_ge_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:45.431376+00:00
-- url     : https://prove2.me/submissions/4609fbec-14fd-4fcd-baef-a11f176c8e5e

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCut
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollifyEqConvolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeakA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {W : Set (V n)} (hW : IsOpen W) {f : V n → ℝ}
    (hf : ContinuousOn f W) (c : ℝ) : MeasurableSet {z | z ∈ W ∧ c ≤ f z} := by
  have h1 : IsOpen (W ∩ f ⁻¹' Set.Iio c) := hf.isOpen_inter_preimage hW isOpen_Iio
  have h2 : {z | z ∈ W ∧ c ≤ f z} = W \ (W ∩ f ⁻¹' Set.Iio c) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_Iio, not_and, not_lt]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun _ => b⟩, fun ⟨a, b⟩ => ⟨a, b a⟩⟩
  rw [h2]
  exact hW.measurableSet.diff h1.measurableSet
end ReciprocityTheory.L2DbarEstimates.C
