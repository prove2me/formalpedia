-- Prove2me | solution 1 for PowerSeries.tsum_coeff_mul_mul_pow_eq_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1e242ca0-31df-5ec6-9196-24fa5113e353

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mul coeff"
p2m_open "PowerSeries"

variable {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]

theorem l1_norm_coeff_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (n : ℕ) :
    ‖PowerSeries.coeff n F‖ ≤ M / ρ ^ n :=
  (le_div_iff₀ (pow_pos hρ n)).mpr (hF n)

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

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (z : L) (hz : ‖z‖ < ρ) :
    ∑' n, PowerSeries.coeff n (F * G) * z ^ n
      = (∑' n, PowerSeries.coeff n F * z ^ n) * ∑' n, PowerSeries.coeff n G * z ^ n := by

  have hr : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hz
  have hr0 : 0 ≤ ‖z‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hFn : Summable (fun n => ‖PowerSeries.coeff n F * z ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ 0))
    simpa using l1_norm_term_le F hρ hF z hz 0 n
  have hGn : Summable (fun n => ‖PowerSeries.coeff n G * z ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left (M' / ρ ^ 0))
    simpa using l1_norm_term_le G hρ hG z hz 0 n
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

#print axioms solution

end S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt
end P2MW
export P2MW.S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt (solution)
