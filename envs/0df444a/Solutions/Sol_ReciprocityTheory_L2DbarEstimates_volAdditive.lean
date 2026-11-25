-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.volAdditive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:41.76064+00:00
-- url     : https://prove2.me/submissions/65c4aa40-6889-48b3-a5c2-f42b959c4d14

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurable_encard_fiber
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
section VolAux
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]
end VolAux
section VolMain
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]
private theorem encard_eq_count {X : Type*} [MeasurableSpace X] (S : Set X) (hS : MeasurableSet S) :
    ((S.encard : ℕ∞) : ℝ≥0∞) = Measure.count S := by
  rw [Measure.count_apply hS]
  all_goals first | rfl | simp
end VolMain
end
end ReciprocityTheory.L2DbarEstimates
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) :
    VolAdditive n z := by
  intro f hf hd
  have hmz : ∀ y : V n, MeasurableSet (z ⁻¹' {y}) :=
    fun y => (measurableSet_singleton y).preimage hz.continuous.measurable
  simp only [volFun]
  have h1 : ∀ y, (((⋃ i, f i) ∩ z ⁻¹' {y}).encard : ℝ≥0∞) =
      ∑' i, ((f i ∩ z ⁻¹' {y}).encard : ℝ≥0∞) := by
    intro y
    rw [encard_eq_count _ ((MeasurableSet.iUnion hf).inter (hmz y)), Set.iUnion_inter,
      measure_iUnion (fun i j hij => ((show Disjoint (f i) (f j) from hd hij).mono
        Set.inter_subset_left Set.inter_subset_left)) (fun i => (hf i).inter (hmz y))]
    congr 1
    funext i
    rw [encard_eq_count _ ((hf i).inter (hmz y))]
  simp_rw [h1]
  exact lintegral_tsum (fun i => (measurable_encard_fiber n z hz (f i) (hf i)).aemeasurable)
end ReciprocityTheory.L2DbarEstimates
