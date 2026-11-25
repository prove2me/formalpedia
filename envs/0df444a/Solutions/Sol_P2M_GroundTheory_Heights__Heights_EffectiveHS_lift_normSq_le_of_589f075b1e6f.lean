-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_normSq_le_of_589f075b1e6f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:06.64086+00:00
-- url     : https://prove2.me/submissions/c202b149-f66e-449d-af27-a67018ed3492

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
open MeasureTheory
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
    (u Ft : ι → X → ℂ) (r G : ι → ℝ) (K B N : ℝ) (hB : 0 ≤ B)
    (hu : ∀ i x, ‖u i x‖ ≤ r i) (hFt : ∀ i, Integrable (fun x => ‖Ft i x‖ ^ 2) μ)
    (hL : ∀ i, ∫ x, ‖Ft i x‖ ^ 2 ∂μ ≤ K * G i ^ 2)
    (hN : N ^ 2 ≤ B * ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ) :
    N ^ 2 ≤ B * K * (Fintype.card ι) * ∑ i, r i ^ 2 * G i ^ 2 := by
  have hpt : ∀ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ‖Ft i x‖ ^ 2 := by
    intro x
    have h1 : ‖∑ i, u i x * Ft i x‖ ≤ ∑ i, r i * ‖Ft i x‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hu i x) (norm_nonneg _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => r i * ‖Ft i x‖)
    calc ‖∑ i, u i x * Ft i x‖ ^ 2 ≤ (∑ i, r i * ‖Ft i x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := by simpa [mul_pow, card_univ] using h2
  have hint : Integrable (fun x => (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ‖Ft i x‖ ^ 2) μ :=
    (integrable_finsetSum _ fun i _ => (hFt i).const_mul (r i ^ 2)).const_mul _
  have hI : ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ ≤
      (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * (K * G i ^ 2) := by
    calc ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ
        ≤ ∫ x, (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ‖Ft i x‖ ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hint
            (Filter.Eventually.of_forall hpt)
      _ = (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ∫ x, ‖Ft i x‖ ^ 2 ∂μ := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => (hFt i).const_mul (r i ^ 2)]
          simp_rw [integral_const_mul]
      _ ≤ _ := by
          gcongr with i
          exact hL i
  calc N ^ 2 ≤ B * ((Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * (K * G i ^ 2)) :=
        hN.trans (mul_le_mul_of_nonneg_left hI hB)
    _ = B * K * (Fintype.card ι) * ∑ i, r i ^ 2 * G i ^ 2 := by
        rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        ring
end GroundTheory.Heights₂.Heights.EffectiveHS
