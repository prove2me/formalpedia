-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.fourier_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:26.108465+00:00
-- url     : https://prove2.me/submissions/0c0cb9a3-c7b3-466f-8b43-b776638ae673

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_smooth
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.RealFourierCoefficientBounds
open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds
theorem _root_.solution (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x w : V),
    ‖𝓕 (H f₁ f₂ x) w‖ * (1 + ‖x‖ + ‖w‖) ^ N ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  obtain ⟨K, hK, h⟩ := H_int (V := V) N
  refine ⟨2 ^ N * (2 * (2 ^ N * ((N + 1) * K))), by positivity, fun f₁ f₂ x w => ?_⟩
  set Q := q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have step : ∀ n ≤ N, (1 + ‖x‖) ^ N * (‖w‖ ^ n * ‖𝓕 (H f₁ f₂ x) w‖) ≤ 2 ^ N * ((N + 1) * K) * Q := by
    intro n hn
    have h1 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := (N : ℕ∞)) (f := H f₁ f₂ x)
      ((H_smooth f₁ f₂ x).of_le (by exact_mod_cast le_top))
      (fun k m hk hm => by
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        simpa using (h f₁ f₂ x m (by exact_mod_cast hm)).1)
      (k := 0) (n := n) (by simp) (by exact_mod_cast hn) w
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
      Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.coeFn_mk] at h1
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 ^ n * ∑ _j ∈ Finset.range (n + 1), K * Q := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
          exact (h f₁ f₂ x j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)).2
      _ = 2 ^ n * ((n + 1) * K) * Q := by simp; ring
      _ ≤ _ := by gcongr; norm_num
  have s0 := step 0 (Nat.zero_le _)
  have sN := step N le_rfl
  have e1 : (1 + ‖x‖ + ‖w‖) ^ N ≤ (1 + ‖x‖) ^ N * (1 + ‖w‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg w)]) N
  have e2 : (1 + ‖w‖) ^ N ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
    have := add_pow_le (zero_le_one' ℝ) (norm_nonneg w) N
    rw [one_pow] at this
    refine this.trans ?_
    gcongr
    · norm_num
    · omega
  calc _ ≤ ‖𝓕 (H f₁ f₂ x) w‖ * ((1 + ‖x‖) ^ N * (2 ^ N * (1 + ‖w‖ ^ N))) := by
        gcongr
        exact e1.trans (by gcongr)
    _ = 2 ^ N * ((1 + ‖x‖) ^ N * (‖w‖ ^ 0 * ‖𝓕 (H f₁ f₂ x) w‖) +
          (1 + ‖x‖) ^ N * (‖w‖ ^ N * ‖𝓕 (H f₁ f₂ x) w‖)) := by ring
    _ ≤ 2 ^ N * (2 ^ N * ((N + 1) * K) * Q + 2 ^ N * ((N + 1) * K) * Q) := by gcongr
    _ = _ := by ring
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
