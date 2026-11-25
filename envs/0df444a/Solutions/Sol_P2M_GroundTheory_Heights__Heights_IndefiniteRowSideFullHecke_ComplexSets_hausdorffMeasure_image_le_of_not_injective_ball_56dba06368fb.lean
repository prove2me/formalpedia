-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_not_injective_ball_56dba06368fb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:35.78741+00:00
-- url     : https://prove2.me/submissions/d1ecc4aa-9971-4c14-96ca-b1ad54c13655

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_pos_hausdorffMeasure_image_le_of_not_injective_b03f868ef36e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
variable [SecondCountableTopology F]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {f : (ι → ℝ) → F} {s : Set (ι → ℝ)}
    {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) (R : ℝ) (hs : s ⊆ closedBall 0 R)
    (ε : ℝ≥0) (εpos : 0 < ε) :
    μH[Fintype.card ι] (f '' s) ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · simp
  have : ∀ A : (ι → ℝ) →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (¬ Function.Injective A →
      ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
        μH[Fintype.card ι] (f '' t) ≤ ε * volume t) := by
    intro A
    by_cases hA : Function.Injective A
    · exact ⟨1, one_pos, fun h => absurd hA h⟩
    · obtain ⟨δ, hδ, h⟩ := exists_pos_hausdorffMeasure_image_le_of_not_injective f A hA εpos
      exact ⟨δ, hδ, fun _ => h⟩
  choose δ hδ using this
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      fun A => (hδ A).1.ne'
  calc
    μH[Fintype.card ι] (f '' s) ≤ μH[Fintype.card ι] (⋃ n, f '' (s ∩ t n)) := by
      rw [← image_iUnion, ← inter_iUnion]
      gcongr
      exact subset_inter Subset.rfl t_cover
    _ ≤ ∑' n, μH[Fintype.card ι] (f '' (s ∩ t n)) := measure_iUnion_le _
    _ ≤ ∑' n, (ε : ℝ≥0∞) * volume (s ∩ t n) := by
      gcongr with n
      obtain ⟨y, ys, hy⟩ := Af' h's n
      exact (hδ (A n)).2 (by rw [hy]; exact hinj y ys) _ (ht n)
    _ ≤ ε * ∑' n, volume (closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [ENNReal.tsum_mul_left]
      gcongr
    _ = ε * volume (⋃ n, closedBall (0 : ι → ℝ) R ∩ t n) := by
      rw [measure_iUnion]
      · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      · intro n
        exact measurableSet_closedBall.inter (t_meas n)
    _ ≤ ε * volume (closedBall (0 : ι → ℝ) R) := by grw [← inter_iUnion, inter_subset_left]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
