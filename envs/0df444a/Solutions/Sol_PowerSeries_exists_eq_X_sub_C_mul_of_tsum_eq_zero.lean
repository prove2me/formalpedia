-- Prove2me | solution 1 for PowerSeries.exists_eq_X_sub_C_mul_of_tsum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/eb5c9080-e13b-5edc-af17-1ce5c3310677

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk coeff_zero_X_mul coeff_C_mul ext C coeff_succ_X_mul coeff X"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

theorem l1_norm_coeff_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (n : ℕ) :
    ‖PowerSeries.coeff n F‖ ≤ M / ρ ^ n :=
  (le_div_iff₀ (pow_pos hρ n)).mpr (hF n)

theorem l1_M_nonneg (F : PowerSeries L) {ρ M : ℝ}
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) : 0 ≤ M := by
  have := hF 0
  simp only [pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

theorem l1_norm_term_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j m : ℕ) :
    ‖PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := by
  rw [norm_mul, norm_pow, div_pow]
  have h1 := l1_norm_coeff_le F hρ hF (j + m)
  rw [pow_add] at h1
  have hρj : 0 < ρ ^ j := pow_pos hρ j
  have hρm : 0 < ρ ^ m := pow_pos hρ m
  calc ‖PowerSeries.coeff (j + m) F‖ * ‖a‖ ^ m
      ≤ M / (ρ ^ j * ρ ^ m) * ‖a‖ ^ m := by gcongr
    _ = M / ρ ^ j * (‖a‖ ^ m / ρ ^ m) := by field_simp

theorem l1_summable_shifted (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j : ℕ) :
    Summable (fun m : ℕ => PowerSeries.coeff (j + m) F * a ^ m) := by
  have hr : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hr0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ j))
    (fun m => l1_norm_term_le F hρ hF a ha j m)

theorem l1_norm_tsum_shifted_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j : ℕ) :
    ‖∑' m : ℕ, PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j := by
  have hM := l1_M_nonneg F hF
  have hC : 0 ≤ M / ρ ^ j := div_nonneg hM (pow_pos hρ j).le
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun m => ?_
  have hr1 : (‖a‖ / ρ) ^ m ≤ 1 :=
    pow_le_one₀ (div_nonneg (norm_nonneg _) hρ.le) ((div_le_one hρ).mpr ha.le)
  calc ‖PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := l1_norm_term_le F hρ hF a ha j m
    _ ≤ M / ρ ^ j * 1 := by gcongr
    _ = M / ρ ^ j := mul_one _

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (hFa : ∑' n, PowerSeries.coeff n F * a ^ n = 0) :
    ∃ H : PowerSeries L, F = (PowerSeries.X - PowerSeries.C a) * H ∧
      ∀ n, ‖PowerSeries.coeff n H‖ * ρ ^ (n + 1) ≤ M := by
  set H : PowerSeries L := PowerSeries.mk fun j => ∑' m : ℕ, PowerSeries.coeff (j + 1 + m) F * a ^ m with hH
  have hHc : ∀ j, PowerSeries.coeff j H = ∑' m : ℕ, PowerSeries.coeff (j + 1 + m) F * a ^ m := fun j => by
    rw [hH, PowerSeries.coeff_mk]

  have htail : ∀ j, a * (∑' m : ℕ, PowerSeries.coeff (j + 1 + m) F * a ^ m)
      = (∑' m : ℕ, PowerSeries.coeff (j + m) F * a ^ m) - PowerSeries.coeff j F := by
    intro j
    have hs := l1_summable_shifted F hρ hF a ha j
    rw [hs.tsum_eq_zero_add]
    simp only [add_zero, pow_zero, mul_one, add_sub_cancel_left]
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    rw [show j + (m + 1) = j + 1 + m by omega, pow_succ]
    ring
  refine ⟨H, ?_, ?_⟩
  · ext n
    rw [sub_mul, map_sub, PowerSeries.coeff_C_mul]
    rcases n with _ | j
    · rw [PowerSeries.coeff_zero_X_mul, hHc]
      have h0 := htail 0
      simp only [zero_add] at h0 ⊢
      rw [hFa] at h0
      linear_combination h0
    · rw [PowerSeries.coeff_succ_X_mul, hHc, hHc]
      have h1 := htail (j + 1)
      linear_combination h1
  · intro j
    rw [hHc]
    exact (le_div_iff₀ (pow_pos hρ (j + 1))).mp (l1_norm_tsum_shifted_le F hρ hF a ha (j + 1))

#print axioms solution

end S_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero
end P2MW
export P2MW.S_PowerSeries_exists_eq_X_sub_C_mul_of_tsum_eq_zero (solution)
