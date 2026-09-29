-- Prove2me | solution 1 for PowerSeries.norm_coeff_taylorShift_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/74becbc3-b38e-5fa5-b4b8-0aa09e2bf35a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_norm_coeff_taylorShift_mul_pow_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_mk mk C coeff"
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

theorem l1_norm_shift_term_le (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (n k : ℕ) :
    ‖PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖ ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := by
  have h := l1_norm_term_le F hρ hF a ha n k
  rw [norm_mul, norm_mul]
  rw [norm_mul] at h
  have hc : ‖((n + k).choose n : L)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one L _
  calc ‖PowerSeries.coeff (n + k) F‖ * ‖((n + k).choose n : L)‖ * ‖a ^ k‖
      ≤ ‖PowerSeries.coeff (n + k) F‖ * 1 * ‖a ^ k‖ := by gcongr
    _ = ‖PowerSeries.coeff (n + k) F‖ * ‖a ^ k‖ := by rw [mul_one]
    _ ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := h

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_norm_coeff_taylorShift_mul_pow_le.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (a : L) (ha : ‖a‖ < ρ) (n : ℕ) :
    Summable (fun k : ℕ => PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) ∧
      ‖PowerSeries.coeff n (PowerSeries.mk fun n => ∑' k : ℕ,
          PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)‖ * ρ ^ n ≤ M := by
  have hr : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hr0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hsum : Summable (fun k : ℕ => PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ n))
      (fun k => l1_norm_shift_term_le F hρ hF a ha n k)
  refine ⟨hsum, ?_⟩
  rw [PowerSeries.coeff_mk]
  have hM := l1_M_nonneg F hF
  have hC : 0 ≤ M / ρ ^ n := div_nonneg hM (pow_pos hρ n).le
  have h : ‖∑' k : ℕ, PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖ ≤ M / ρ ^ n := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun k => ?_
    have hr1 : (‖a‖ / ρ) ^ k ≤ 1 := pow_le_one₀ hr0 hr.le
    calc ‖PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k‖
        ≤ M / ρ ^ n * (‖a‖ / ρ) ^ k := l1_norm_shift_term_le F hρ hF a ha n k
      _ ≤ M / ρ ^ n * 1 := by gcongr
      _ = M / ρ ^ n := mul_one _
  exact (le_div_iff₀ (pow_pos hρ n)).mp h

#print axioms solution

end S_PowerSeries_norm_coeff_taylorShift_mul_pow_le
end P2MW
export P2MW.S_PowerSeries_norm_coeff_taylorShift_mul_pow_le (solution)
