-- Prove2me | solution 1 for PowerSeries.eq_of_forall_tsum_coeff_mul_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/c786c855-5a37-504a-9ca2-671581544daa

import Mathlib
import Theorems.Thm_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace PowerSeries
p2m_export "PowerSeries" "coeff_order order coeff_of_lt_order coeff order_eq_top summable_and_norm_tsum_coeff_mul_pow_le"
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

theorem l1_tsum_eq_pow_mul_tsum_of_forall_lt (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (z : L) (hz : ‖z‖ < ρ)
    (n₀ : ℕ) (h0 : ∀ n < n₀, PowerSeries.coeff n F = 0) :
    ∑' n, PowerSeries.coeff n F * z ^ n = z ^ n₀ * ∑' m : ℕ, PowerSeries.coeff (n₀ + m) F * z ^ m := by
  have hs := (summable_and_norm_tsum_coeff_mul_pow_le F hρ hF z hz).1
  rw [← hs.sum_add_tsum_nat_add n₀, Finset.sum_eq_zero (fun n hn => by
      rw [Finset.mem_range] at hn
      rw [h0 n hn, zero_mul]), zero_add, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [add_comm m n₀, pow_add]
  ring

theorem eq_zero_of_forall_tsum_coeff_mul_pow_eq_zero
    (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
    (h : ∀ z : L, ‖z‖ < ρ → ∑' n, PowerSeries.coeff n F * z ^ n = 0) : F = 0 := by
  by_contra hne
  set n₀ : ℕ := F.order.toNat with hn₀
  have hn₀' : F.order = n₀ := by
    rw [hn₀, ENat.coe_toNat]
    exact PowerSeries.order_eq_top.not.mpr hne
  have hc : PowerSeries.coeff n₀ F ≠ 0 := by
    have := PowerSeries.coeff_order hne
    exact this
  have hlt : ∀ n < n₀, PowerSeries.coeff n F = 0 := fun n hn =>
    PowerSeries.coeff_of_lt_order n (by rw [hn₀']; exact_mod_cast hn)

  have hM := l1_M_nonneg F hF

  obtain ⟨z, hz0, hzlt⟩ := NormedField.exists_norm_lt L
    (lt_min hρ (div_pos (mul_pos (norm_pos_iff.mpr hc) (pow_pos hρ (n₀ + 1))) (by linarith : (0:ℝ) < M + 1)))
  have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hzlt (min_le_left _ _)
  have hzc : ‖z‖ < ‖PowerSeries.coeff n₀ F‖ * ρ ^ (n₀ + 1) / (M + 1) := lt_of_lt_of_le hzlt (min_le_right _ _)

  have hev := h z hzρ
  rw [l1_tsum_eq_pow_mul_tsum_of_forall_lt F hρ hF z hzρ n₀ hlt] at hev
  have hz0' : z ≠ 0 := norm_pos_iff.mp hz0
  have hE : ∑' m : ℕ, PowerSeries.coeff (n₀ + m) F * z ^ m = 0 :=
    (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ hz0')

  have hs := l1_summable_shifted F hρ hF z hzρ n₀
  rw [hs.tsum_eq_zero_add] at hE
  simp only [add_zero, pow_zero, mul_one] at hE
  have hE1 : ‖∑' m : ℕ, PowerSeries.coeff (n₀ + (m + 1)) F * z ^ (m + 1)‖
      ≤ ‖z‖ * (M / ρ ^ (n₀ + 1)) := by
    have heq : ∑' m : ℕ, PowerSeries.coeff (n₀ + (m + 1)) F * z ^ (m + 1)
        = z * ∑' m : ℕ, PowerSeries.coeff (n₀ + 1 + m) F * z ^ m := by
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      rw [show n₀ + (m + 1) = n₀ + 1 + m by omega, pow_succ]
      ring
    rw [heq, norm_mul]
    gcongr
    exact l1_norm_tsum_shifted_le F hρ hF z hzρ (n₀ + 1)

  have heq2 : PowerSeries.coeff n₀ F = -∑' m : ℕ, PowerSeries.coeff (n₀ + (m + 1)) F * z ^ (m + 1) :=
    eq_neg_of_add_eq_zero_left hE
  have hnorm : ‖PowerSeries.coeff n₀ F‖ ≤ ‖z‖ * (M / ρ ^ (n₀ + 1)) := by
    rw [heq2, norm_neg]
    exact hE1
  have hρn : 0 < ρ ^ (n₀ + 1) := pow_pos hρ _
  have h3 : ‖z‖ * (M / ρ ^ (n₀ + 1)) < ‖PowerSeries.coeff n₀ F‖ := by
    rw [lt_div_iff₀ (by linarith : (0:ℝ) < M + 1)] at hzc
    rw [mul_div_assoc', div_lt_iff₀ hρn]
    nlinarith [norm_nonneg z, norm_nonneg (PowerSeries.coeff n₀ F)]
  linarith

end PowerSeries

open _root_.PowerSeries _root_.P2MW.S_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq.PowerSeries in

theorem solution {L : Type*} [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
    (F G : PowerSeries L) {ρ M M' : ℝ} (hρ : 0 < ρ)
    (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
    (h : ∀ z : L, ‖z‖ < ρ → ∑' n, PowerSeries.coeff n F * z ^ n = ∑' n, PowerSeries.coeff n G * z ^ n) :
    F = G := by
  have hFG : ∀ n, ‖PowerSeries.coeff n (F - G)‖ * ρ ^ n ≤ max M M' := by
    intro n
    rw [map_sub]
    have hρn : 0 ≤ ρ ^ n := (pow_pos hρ n).le
    calc ‖PowerSeries.coeff n F - PowerSeries.coeff n G‖ * ρ ^ n
        ≤ max ‖PowerSeries.coeff n F‖ ‖PowerSeries.coeff n G‖ * ρ ^ n := by
          gcongr
          calc ‖PowerSeries.coeff n F - PowerSeries.coeff n G‖
              = ‖PowerSeries.coeff n F + -PowerSeries.coeff n G‖ := by rw [sub_eq_add_neg]
            _ ≤ max ‖PowerSeries.coeff n F‖ ‖-PowerSeries.coeff n G‖ := IsUltrametricDist.norm_add_le_max _ _
            _ = max ‖PowerSeries.coeff n F‖ ‖PowerSeries.coeff n G‖ := by rw [norm_neg]
      _ = max (‖PowerSeries.coeff n F‖ * ρ ^ n) (‖PowerSeries.coeff n G‖ * ρ ^ n) :=
          (max_mul_of_nonneg _ _ hρn)
      _ ≤ max M M' := max_le_max (hF n) (hG n)
  have h0 := eq_zero_of_forall_tsum_coeff_mul_pow_eq_zero (F - G) hρ hFG (fun z hz => by
    have hs1 := (summable_and_norm_tsum_coeff_mul_pow_le F hρ hF z hz).1
    have hs2 := (summable_and_norm_tsum_coeff_mul_pow_le G hρ hG z hz).1
    simp only [map_sub, sub_mul]
    rw [hs1.tsum_sub hs2, h z hz, sub_self])
  exact sub_eq_zero.mp h0

#print axioms solution

end S_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq
end P2MW
export P2MW.S_PowerSeries_eq_of_forall_tsum_coeff_mul_pow_eq (solution)
