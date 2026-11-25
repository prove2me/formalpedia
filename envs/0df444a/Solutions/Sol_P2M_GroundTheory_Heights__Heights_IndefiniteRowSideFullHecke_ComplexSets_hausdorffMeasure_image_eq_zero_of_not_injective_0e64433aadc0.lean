-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_eq_zero_of_not_injective_0e64433aadc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:46.842428+00:00
-- url     : https://prove2.me/submissions/b2d28978-65d9-4e07-9226-61c833823975

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_not_injective_ball_56dba06368fb

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
    (hinj : ∀ x ∈ s, ¬ Function.Injective (f' x)) :
    μH[Fintype.card ι] (f '' s) = 0 := by
  suffices H : ∀ R, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) = 0 by
    rw [← nonpos_iff_eq_zero, ← iUnion_inter_closedBall_nat s 0]
    calc
      μH[Fintype.card ι] (f '' ⋃ n : ℕ, s ∩ closedBall 0 n)
          ≤ ∑' n : ℕ, μH[Fintype.card ι] (f '' (s ∩ closedBall 0 n)) := by
        rw [image_iUnion]; exact measure_iUnion_le _
      _ ≤ 0 := by simp only [H, tsum_zero, le_refl]
  intro R
  have hA : ∀ ε : ℝ≥0, 0 < ε →
      μH[Fintype.card ι] (f '' (s ∩ closedBall 0 R)) ≤ ε * volume (closedBall (0 : ι → ℝ) R) :=
    fun ε εpos => hausdorffMeasure_image_le_of_not_injective_ball
      (fun x hx => (hf' x hx.1).mono inter_subset_left) (fun x hx => hinj x hx.1) R
      inter_subset_right ε εpos
  have hB : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun ε : ℝ≥0 => (ε : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R)) (𝓝 0)
        (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : ι → ℝ) R))) :=
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr measure_closedBall_lt_top.ne)
    simp only [zero_mul, ENNReal.coe_zero] at this
    exact Tendsto.mono_left this nhdsWithin_le_nhds
  rw [← nonpos_iff_eq_zero]
  apply ge_of_tendsto hB
  filter_upwards [self_mem_nhdsWithin]
  exact hA
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
