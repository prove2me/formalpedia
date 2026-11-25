-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.measurable_encard_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:10.839185+00:00
-- url     : https://prove2.me/submissions/4e49069a-fb8e-4129-b592-58f15993011f

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_cover
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurableSet_image_of_isLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_encard_inter_fiber_of_injOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_injOn_source_of_chart
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
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M]
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (A : Set M)
    (hA : MeasurableSet A) :
    Measurable fun y => (((A ∩ z ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞) := by
  obtain ⟨T, hTo, hTU, hTc⟩ := exists_chart_cover n z hz
  have hmz : ∀ y : V n, MeasurableSet (z ⁻¹' {y}) :=
    fun y => (measurableSet_singleton y).preimage hz.continuous.measurable
  have hDm : ∀ i, MeasurableSet (disjointed T i) :=
    MeasurableSet.disjointed (fun i => (hTo i).measurableSet)
  have hDd : Pairwise (Function.onFun Disjoint (disjointed T)) := disjoint_disjointed T
  have hDU : ⋃ i, disjointed T i = Set.univ := by rw [iUnion_disjointed, hTU]
  have hDT : ∀ i, disjointed T i ⊆ T i := disjointed_subset T
  have injA : ∀ i, InjOn z (A ∩ disjointed T i) := by
    intro i
    rcases hTc i with h | ⟨e, he, hTe⟩
    · have h2 : A ∩ disjointed T i = ∅ :=
        Set.subset_empty_iff.mp (Set.inter_subset_right.trans ((hDT i).trans h.subset))
      rw [h2]; exact Set.injOn_empty z
    · exact (injOn_source_of_chart n z e he).mono
        (Set.inter_subset_right.trans ((hDT i).trans hTe))
  have key : ∀ y, ((A ∩ z ⁻¹' {y}).encard : ℝ≥0∞) =
      ∑' i, (z '' (A ∩ disjointed T i)).indicator 1 y := by
    intro y
    have h3 : A ∩ z ⁻¹' {y} = ⋃ i, (A ∩ disjointed T i) ∩ z ⁻¹' {y} := by
      rw [← Set.iUnion_inter, ← Set.inter_iUnion, hDU, Set.inter_univ]
    rw [encard_eq_count _ (hA.inter (hmz y)), h3,
      measure_iUnion (fun i j hij => ((show Disjoint (disjointed T i) (disjointed T j) from hDd hij).mono
        (Set.inter_subset_left.trans Set.inter_subset_right)
        (Set.inter_subset_left.trans Set.inter_subset_right)))
        (fun i => (hA.inter (hDm i)).inter (hmz y))]
    congr 1
    funext i
    rw [← encard_eq_count _ ((hA.inter (hDm i)).inter (hmz y)),
      encard_inter_fiber_of_injOn n z _ (injA i) y]
  have h4 : (fun y => ((A ∩ z ⁻¹' {y}).encard : ℝ≥0∞)) =
      fun y => ∑' i, (z '' (A ∩ disjointed T i)).indicator 1 y := funext key
  rw [h4]
  exact Measurable.ennreal_tsum (fun i => measurable_one.indicator
    (measurableSet_image_of_isLocalHomeomorph n z hz _ (hA.inter (hDm i))))
end ReciprocityTheory.L2DbarEstimates
