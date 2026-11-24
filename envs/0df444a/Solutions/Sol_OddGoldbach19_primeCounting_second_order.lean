-- Prove2me | solution 1 for OddGoldbach19.primeCounting_second_order
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T16:21:19.776194+00:00
-- url     : https://prove2.me/submissions/7f5c2b1a-432a-4989-8b8a-d63de649a31b

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic

set_option autoImplicit false
open Real MeasureTheory

namespace OddGoldbach19

theorem exp20_ge : (3125 : ℝ) ≤ exp 20 := by
  have h := add_one_le_exp (4 : ℝ)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) (show (5 : ℝ) ≤ exp 4 by linarith) 5
  have he : exp 20 = exp 4 ^ 5 := by rw [← exp_nat_mul]; norm_num
  rw [← he] at hp
  norm_num at hp
  exact hp

theorem log100_le : log (100 : ℝ) ≤ 7 := by
  calc log (100 : ℝ) ≤ log ((2 : ℝ) ^ 7) := log_le_log (by norm_num) (by norm_num)
    _ = 7 * log 2 := by rw [log_pow]; norm_num
    _ ≤ 7 := by linarith [log_two_lt_d9]

theorem theta_lower_0975 (x : ℝ) (hx : 0 < x) (hl : 20 ≤ log x) :
    (0.975 : ℝ) * x ≤ Chebyshev.theta x := by
  have h1340 : (1340 : ℝ) ≤ x := by
    have he : exp 20 ≤ x := by rw [← exp_log hx]; exact exp_le_exp.2 hl
    linarith [exp20_ge]
  have ht := TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic x h1340
  have hi : 1 / (2 * log x) ≤ (0.025 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  nlinarith

end OddGoldbach19
open OddGoldbach19
/-- A positive second-order prime-counting term from the existing theta estimate. -/
theorem solution (n : ℕ) (hl : 100 ≤ log (n : ℝ)) :
    (n : ℝ) / log n + 0.46 * n / (log n) ^ 2 ≤ (Nat.primeCounting n : ℝ) := by
  have hnpos : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    norm_num at hl
  have hxpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlpos : 0 < log (n : ℝ) := by linarith
  have hax : (n : ℝ) / 100 ≤ n := by linarith
  have hapos : (0 : ℝ) < (n : ℝ) / 100 := by positivity
  have hla : 20 ≤ log ((n : ℝ) / 100) := by
    rw [log_div (ne_of_gt hxpos) (by norm_num)]
    linarith [log100_le]
  have ha2 : (2 : ℝ) ≤ (n : ℝ) / 100 := by
    have he : exp 20 ≤ (n : ℝ) / 100 := by
      rw [← exp_log hapos]
      exact exp_le_exp.2 hla
    linarith [exp20_ge]
  have hx2 : (2 : ℝ) ≤ n := by linarith
  let f : ℝ → ℝ := fun t => Chebyshev.theta t / (t * log t ^ 2)
  have hfull : IntervalIntegrable f volume 2 (n : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx2).2
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq n)
  have hleft : IntervalIntegrable f volume 2 ((n : ℝ) / 100) := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le ha2, Set.uIcc_of_le hx2]
    exact Set.Icc_subset_Icc le_rfl hax
  have hright : IntervalIntegrable f volume ((n : ℝ) / 100) (n : ℝ) := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hax, Set.uIcc_of_le hx2]
    exact Set.Icc_subset_Icc ha2 le_rfl
  have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..((n : ℝ) / 100), f t := by
    apply intervalIntegral.integral_nonneg ha2
    intro t ht
    exact div_nonneg (Chebyshev.theta_nonneg t) (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
  have hmono : (∫ t in ((n : ℝ) / 100)..(n : ℝ), f t) ≤ ∫ t in (2 : ℝ)..(n : ℝ), f t := by
    have he := intervalIntegral.integral_add_adjacent_intervals hleft hright
    linarith
  have hpoint : ∀ t ∈ Set.Icc ((n : ℝ) / 100) (n : ℝ),
      (0.975 : ℝ) / (log n) ^ 2 ≤ f t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hapos ht.1
    have hlt : 20 ≤ log t := hla.trans (log_le_log hapos ht.1)
    have hltpos : 0 < log t := by linarith
    have hltn : log t ≤ log (n : ℝ) := log_le_log htpos ht.2
    have htheta := theta_lower_0975 t htpos hlt
    calc (0.975 : ℝ) / (log n) ^ 2 ≤ 0.975 / (log t) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ hltpos.le hltn 2)
      _ = (0.975 * t) / (t * log t ^ 2) := by field_simp
      _ ≤ f t := div_le_div_of_nonneg_right htheta (by positivity)
  have hint := intervalIntegral.integral_mono_on hax
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0.975 : ℝ) / log (n : ℝ) ^ 2) volume _ _)
    hright hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hint
  have hi : ((n : ℝ) - (n : ℝ) / 100) * (0.975 / log (n : ℝ) ^ 2) ≤
      ∫ t in (2 : ℝ)..(n : ℝ), f t := hint.trans hmono
  have h1340 : (1340 : ℝ) ≤ n := by
    have he : exp 20 ≤ (n : ℝ) := by rw [← exp_log hxpos]; exact exp_le_exp.2 (by linarith)
    linarith [exp20_ge]
  have ht := (TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic (n : ℝ) h1340).le
  have htdiv := div_le_div_of_nonneg_right ht hlpos.le
  have hformula := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  simp only [Nat.floor_natCast] at hformula
  have he : ((n : ℝ) * (1 - 1 / (2 * log (n : ℝ)))) / log n +
      ((n : ℝ) - (n : ℝ) / 100) * (0.975 / log (n : ℝ) ^ 2) =
      (n : ℝ) / log n + 0.46525 * n / log (n : ℝ) ^ 2 := by
    field_simp
    ring
  calc (n : ℝ) / log n + 0.46 * n / log (n : ℝ) ^ 2 ≤
      (n : ℝ) / log n + 0.46525 * n / log (n : ℝ) ^ 2 := by gcongr <;> norm_num
    _ = _ := he.symm
    _ ≤ _ := add_le_add htdiv hi
    _ = (Nat.primeCounting n : ℝ) := hformula.symm

#print axioms solution

