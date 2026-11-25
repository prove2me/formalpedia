-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBound_PackingCount_card_mul_le_f6acee0bf2de
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:36.092459+00:00
-- url     : https://prove2.me/submissions/f95e1dc3-fb07-4495-a148-4cd9bb9e5374

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CountingLowerBound_PPackingCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBound
open MeasureTheory Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBound
namespace PackingCount
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) {lam R : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hT : ∀ x ∈ T, ‖x‖ < R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lam ≤ ‖x - y‖) :
    (T.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E ≤ (R + lam / 2) ^ Module.finrank ℝ E := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  set d := Module.finrank ℝ E
  have hd : Set.PairwiseDisjoint (↑T : Set E) (fun x => ball x (lam / 2)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ T, ball x (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball] at hz ⊢
    have h1 : dist x 0 < R := by rw [dist_zero_right]; exact hT x hx
    have h2 := dist_triangle z x 0
    linarith
  have h2 := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)] at h2
  rw [Finset.sum_congr rfl (fun x _ => Measure.addHaar_ball_of_pos μ x (half_pos hlam))] at h2
  rw [Finset.sum_const, nsmul_eq_mul, Measure.addHaar_ball_of_pos μ (0 : E) (r := R + lam / 2) (by positivity),
    ← mul_assoc] at h2
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hc1 : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hc0 hc1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
    (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  exact h2
end PackingCount
end GroundTheory.Heights₂.Heights.LowerBound
