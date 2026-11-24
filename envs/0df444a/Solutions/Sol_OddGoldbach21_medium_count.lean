-- Prove2me | solution 1 for OddGoldbach21.medium_count
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-30T09:54:17.36698+00:00
-- url     : https://prove2.me/submissions/af38c379-ba00-4ce7-8663-aa1466c6963a

import Theorems.Thm_OAI_OddGoldbach23_finite_sieve_certificate
import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Theorems.Thm_TaoFivePrimes_siebert_prime_pair_bound
import Definitions.Def_TaoFivePrimes_SingularSeries
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic
import Mathlib

namespace OddGoldbach21
/-- Strong prime-counting input from the existing Rosser--Schoenfeld theorem. -/
theorem primeCounting_lower18 (n : ℕ) (hn : 1340 ≤ n) (hl : 18 ≤ Real.log n) :
    (0.972 : ℝ) * n / Real.log n ≤ (Nat.primeCounting n : ℝ) := by
  have hlog : 0 < Real.log (n : ℝ) := by linarith
  have htheta := TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic (n : ℝ) (by exact_mod_cast hn)
  have hupper := Chebyshev.theta_le_pi_mul_log n
  have hinv : 1 / (2 * Real.log (n : ℝ)) ≤ (0.028 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    linarith
  apply (div_le_iff₀ hlog).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith
end OddGoldbach21

namespace Chebyshev
open Real

theorem Ioc_eq_Icc {n : ℕ} : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

theorem log3_bounds : 1.0986 ≤ Real.log 3 ∧ Real.log 3 ≤ 1.0987 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/4 : ℝ)) (by norm_num [abs_of_pos]) 8
  have e : Real.log (1 - 1/4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 - 1/4 : ℝ) = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]

theorem log5_bounds : 1.60943 ≤ Real.log 5 ∧ Real.log 5 ≤ 1.60944 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1/5 : ℝ)) (by norm_num [abs_of_pos]) 8
  have e : Real.log (1 - 1/5 : ℝ) = 2 * Real.log 2 - Real.log 5 := by
    rw [show (1 - 1/5 : ℝ) = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [e] at h
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_two_lt_d9
  norm_num [Finset.sum_range_succ, abs_le] at h
  constructor <;> nlinarith [h.1, h.2]


open Real Finsupp Finset
open ArithmeticFunction hiding log

attribute [local fun_prop] DifferentiableAt.differentiableWithinAt

noncomputable def T (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, log n

theorem T.le (x : ℝ) (hx : 1 ≤ x) : T x ≤ x * log x - x + 1 + log x := by
  rw [T, ← Ico_insert_right <| Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne',
    sum_insert right_notMem_Ico]
  have : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) :=
    fun a ha _ _ hab ↦ log_le_log (lt_of_lt_of_le one_pos (by grind)) hab
  have : ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 :=
    calc ∑ n ∈ Finset.Ico 1 ⌊x⌋₊, log n
        ≤ ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t := this.sum_le_integral_Ico <|
          Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by simp_all
  have h3 : ∀ t ∈ interior (Set.Ici 1), DifferentiableWithinAt ℝ (_root_.id * log - _root_.id) (interior (Set.Ici 1)) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    fun_prop ( disch := positivity )
  have h4 : ∀ t ∈ interior (Set.Ici 1), 0 ≤ deriv (fun t ↦ t * log t - t) t := by
    intro t ht
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at ht
    have : DifferentiableAt ℝ (fun t ↦ t * log t) t := by fun_prop ( disch := positivity )
    have hderiv : deriv (fun t ↦ t * log t - t) t = log t := by
      simp [show (fun t ↦ t * log t - t) = (fun t ↦ t * log t) - _root_.id by rfl,
        deriv_sub this differentiableAt_id, deriv_mul_log (by linarith)]
    exact hderiv ▸ log_nonneg (le_of_lt ht)
  have h5 : ContinuousOn (fun t ↦ t * log t - t) (Set.Ici 1) := by fun_prop
  have h2 : MonotoneOn (fun t ↦ t * log t - t) (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 1) h5 h3 h4
  have : (⌊x⌋₊ : ℝ) * log ⌊x⌋₊ - ⌊x⌋₊ ≤ x * log x - x := by
    exact h2 (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr hx) <| Nat.floor_le (by grind)
  linarith [log_le_log (by positivity) <| Nat.floor_le (by linarith)]

theorem T.ge (x : ℝ) (hx : 1 ≤ x) : T x ≥ x * log x - x + 1 - log x := by
  have hone_le_floor : 1 ≤ ⌊x⌋₊ := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr hx).ne'
  simp only [T, ← Ico_insert_right hone_le_floor, sum_insert right_notMem_Ico]
  have mono_log : MonotoneOn log (Set.Icc (1 : ℕ) ⌊x⌋₊) := fun a ha _ _ hab ↦
    log_le_log (lt_of_lt_of_le one_pos (by simpa using ha.1)) hab
  have h1 : ∀ n ≥ 1, ∑ i ∈ Ico 1 n, log (i + 1 : ℕ) = log n + ∑ i ∈ Ico 1 n, log i := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih => grind [Nat.Ico_succ_right_eq_insert_Ico]
  have sum_shift : ∑ i ∈ Ico 1 ⌊x⌋₊, log (i + 1 : ℕ) = log ⌊x⌋₊ + ∑ i ∈ Ico 1 ⌊x⌋₊, log i := by
    exact h1 ⌊x⌋₊ hone_le_floor
  have int_le_T : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t ≤ log ⌊x⌋₊ + ∑ n ∈ Ico 1 ⌊x⌋₊, log n := by
    linarith [mono_log.integral_le_sum_Ico hone_le_floor]
  have int_eq : ∫ t in (1 : ℕ)..(⌊x⌋₊ : ℕ), log t = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by simp
  have h2 : ∫ t in (⌊x⌋₊ : ℝ)..x, log t ≤ (x - ⌊x⌋₊) * log x := by
    calc ∫ t in (⌊x⌋₊ : ℝ)..x, log t
      ≤ ∫ _ in (⌊x⌋₊ : ℝ)..x, log x := (intervalIntegral.integral_mono_on (Nat.floor_le <| by linarith) intervalIntegral.intervalIntegrable_log'
            intervalIntegrable_const fun t ht ↦ log_le_log (lt_of_lt_of_le (by positivity) ht.1) ht.2)
      _ = (x - ⌊x⌋₊) * log x := by simp
  have target_le_int : x * log x - x + 1 - log x ≤ ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by
    calc x * log x - x + 1 - log x
        ≤ (x * log x - x + 1) - (x - ⌊x⌋₊) * log x := by nlinarith [log_nonneg hx, Nat.lt_floor_add_one x]
      _ ≤ (x * log x - x + 1) - ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by grind
      _ = ⌊x⌋₊ * log ⌊x⌋₊ - ⌊x⌋₊ + 1 := by grind [integral_log]
  linarith

theorem T.eq_sum_Lambda (x : ℝ) : T x = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * ⌊x / n⌋₊ := by
  unfold T
  simp_rw [← log_apply, ← vonMangoldt_mul_zeta]
  rw [← Ioc_eq_Icc, sum_Ioc_mul_zeta_eq_sum]
  simp [Nat.floor_div_natCast]

noncomputable def E (ν : ℕ →₀ ℝ) (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * ⌊ x / m ⌋₊)

theorem T.weighted_eq_sum (ν : ℕ →₀ ℝ) (x : ℝ) : ν.sum (fun m w ↦ w * T (x/m)) = ∑ n ∈ Icc 1 ⌊x⌋₊, Λ n * E ν (x/n) := by
  simp_rw [T.eq_sum_Lambda, E, Finsupp.mul_sum]
  rw [← sum_finsetSum_comm]
  apply Finsupp.sum_congr fun y hy ↦ ?_
  rw [Finset.mul_sum]
  by_cases hy : y = 0
  · simp [hy]
  have one_le_y : 1 ≤ (y : ℝ) := by grind [Nat.one_le_cast]
  by_cases hx : x < 1
  · simp [hx, show x / y < 1 from div_lt_one (by linarith)|>.mpr (by linarith)]
  apply sum_subset_zero_on_sdiff
  · apply Icc_subset_Icc_right
    gcongr
    exact div_le_self (by linarith) one_le_y
  · intro t ht
    simp only [mem_sdiff, mem_Icc, not_and, not_le] at ht
    simp only [mul_eq_zero, Nat.cast_eq_zero, Nat.floor_eq_zero]
    right
    right
    apply div_lt_one (by linarith)|>.mpr
    have := ht.2 ht.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · grind

open Finsupp in
noncomputable def ν : ℕ →₀ ℝ := single 1 1 - single 2 1 - single 3 1 - single 5 1 + single 30 1

/-- The support of `ν` is `{1, 2, 3, 5, 30}`. Used whenever we need to unfold `ν.sum`. -/
private lemma ν_support : ν.support = {1, 2, 3, 5, 30} := by
  norm_num [ν, Finset.ext_iff]; grind

/-- Unfold `ν.sum (fun m w ↦ w * f m)` into its five-term expansion.
This avoids repeating the `sum_add_index` / `sum_sub_index` chain every time
we need to compute a `ν`-weighted sum. -/
private lemma ν_sum_mul (f : ℕ → ℝ) :
    ν.sum (fun m w ↦ w * f m) = f 1 - f 2 - f 3 - f 5 + f 30 := by
  rw [ν, sum_add_index (by simp) (by intros; ring)]
  grind only [sum_single_index, sum_sub_index]

/-- Unfold `E ν y` into an explicit expression in terms of floors of `y / k`.
This is the key formula repeatedly used to analyse `E ν`. -/
private lemma E_nu_expand (y : ℝ) :
    E ν y = ⌊y⌋₊ - ⌊y / 2⌋₊ - ⌊y / 3⌋₊ - ⌊y / 5⌋₊ + ⌊y / 30⌋₊ := by
  rw [E, ν, sum_add_index' (by grind) (by grind)]
  grind [sum_single_index, sum_sub_index]

/-- The classical sandwich `k * ⌊y/k⌋₊ ≤ ⌊y⌋₊ < k * ⌊y/k⌋₊ + k` for `k ≥ 1` and `y ≥ 0`. -/
private lemma floor_div_bounds {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : 1 ≤ k) :
    k * ⌊y / k⌋₊ ≤ ⌊y⌋₊ ∧ ⌊y⌋₊ < k * ⌊y / k⌋₊ + k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hdivnn : 0 ≤ y / k := div_nonneg hy hk'.le
  refine ⟨Nat.le_floor ?_, ?_⟩
  · push_cast
    have := Nat.floor_le hdivnn
    calc ((k : ℝ) * ⌊y / k⌋₊) = k * (y / k) - k * (y / k - ⌊y / k⌋₊) := by ring
      _ ≤ k * (y / k) := by nlinarith [Nat.floor_le hdivnn]
      _ = y := mul_div_cancel₀ _ hk'.ne'
  · have hlt : y / k < ⌊y / k⌋₊ + 1 := Nat.lt_floor_add_one (y / k)
    have hy_lt : y < (k : ℝ) * (⌊y / k⌋₊ + 1) := by linarith [(div_lt_iff₀ hk').mp hlt]
    have : (⌊y⌋₊ : ℝ) < (k : ℝ) * (⌊y / k⌋₊ + 1) := (Nat.floor_le hy).trans_lt hy_lt
    exact_mod_cast this

theorem nu_sum_div_eq_zero : ν.sum (fun n w ↦ w / n) = 0 := by
  norm_num [ν, add_div, sum_add_index', sub_div, sum_sub_index]

theorem E_nu_eq_one (x : ℝ) (hx : x ∈ Set.Ico 1 6) : E ν x = 1 := by
  obtain ⟨h1, h6⟩ := hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : x / 30 < 1)]
  have hflb : 1 ≤ ⌊x⌋₊ := by rwa [Nat.one_le_floor_iff]
  have hfub : ⌊x⌋₊ ≤ 5 := Nat.lt_succ_iff.mp (Nat.floor_lt' (by grind) |>.mpr h6)
  have h2 := floor_div_bounds hx0 (k := 2) (by norm_num)
  have h3 := floor_div_bounds hx0 (k := 3) (by norm_num)
  have h5 := floor_div_bounds hx0 (k := 5) (by norm_num)
  push_cast at h2 h3 h5
  rw [show ⌊x⌋₊ = ⌊x / 2⌋₊ + ⌊x / 3⌋₊ + ⌊x / 5⌋₊ + 1 by omega]
  grind

theorem E_nu_period (x : ℝ) (hx : x ≥ 0) : E ν (x + 30) = E ν x := by
  have h (k : ℝ) : (x + 30) / k = x / k + (30 / k) := by ring
  simp_rw [E_nu_expand, h 2, h 3, h 5, h 30]
  norm_num
  repeat rw [Nat.floor_add_ofNat (by positivity)]
  rw [Nat.floor_add_one (by positivity)]
  grind

theorem E_nu_bound (x : ℝ) (hx : x ≥ 0) : 0 ≤ E ν x ∧ E ν x ≤ 1 := by
  have : ∀ y, 0 ≤ y → y < 30 → 0 ≤ E ν y ∧ E ν y ≤ 1 := fun y hy0 hy30 ↦ by
    simp only [E_nu_expand, Nat.floor_eq_zero.mpr (by linarith : y / 30 < 1), Nat.cast_zero, add_zero]
    have h2 := floor_div_bounds hy0 (k := 2) (by norm_num)
    have h3 := floor_div_bounds hy0 (k := 3) (by norm_num)
    have h5 := floor_div_bounds hy0 (k := 5) (by norm_num)
    push_cast at h2 h3 h5
    have hfy : ⌊y⌋₊ < 30 := Nat.floor_lt' (by norm_num) |>.mpr (by exact_mod_cast hy30)
    have hlb : ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ ≤ ⌊y⌋₊ := by omega
    have hub : ⌊y⌋₊ ≤ ⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 := by omega
    have hlb' : ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hlb
    have hub' : ((⌊y⌋₊ : ℕ) : ℝ) ≤ ((⌊y/2⌋₊ + ⌊y/3⌋₊ + ⌊y/5⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hub
    push_cast at hlb' hub'
    refine ⟨by linarith, by linarith⟩
  let y := x - ⌊x / 30⌋₊ * 30
  have hy : 0 ≤ y ∧ y < 30 := ⟨by linarith [Nat.floor_le (by positivity : 0 ≤ x/30)], by
    linarith [Nat.lt_floor_add_one (x/30)]⟩
  have hxy : E ν x = E ν y := by
    have : x = y + ⌊x/30⌋₊ * 30 := by ring
    rw [this]; induction ⌊x/30⌋₊ with
    | zero => simp
    | succ n ih => simp [add_mul, ← add_assoc, E_nu_period _ (by linarith : y + n * 30 ≥ 0), ih]
  exact hxy ▸ this y hy.1 hy.2

noncomputable def U (x : ℝ) : ℝ := ν.sum (fun m w ↦ w * T (x/m))

theorem psi_ge_weighted (x : ℝ) (hx : x > 0) : ψ x ≥ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  gcongr with i
  have := E_nu_bound (x / i) (div_nonneg hx.le (by simp))
  grw [this.2, mul_one]

theorem psi_diff_le_weighted (x : ℝ) (hx : x > 0) : ψ x - ψ (x / 6) ≤ U x := by
  unfold U psi
  rw [T.weighted_eq_sum, ← Ioc_eq_Icc]
  have subset : Ioc 0 ⌊x / 6⌋₊ ⊆ Ioc 0 ⌊x⌋₊ := by
    apply Ioc_subset_Ioc_right
    gcongr
    exact div_le_self hx.le (by norm_num)
  rw [← sum_sdiff_eq_sub subset, ← sum_sdiff subset]
  refine le_add_of_le_of_nonneg (sum_le_sum fun n hn ↦ ?_) (sum_nonneg fun n hn ↦ mul_nonneg vonMangoldt_nonneg ?_)
  · rw [E_nu_eq_one, mul_one]
    simp_all only [gt_iff_lt, Finset.mem_sdiff, Finset.mem_Ioc, not_and, not_le, Set.mem_Ico]
    refine ⟨one_le_div (by simp; grind)|>.mpr <| Nat.le_floor_iff hx.le |>.mp hn.1.2, ?_⟩
    have := hn.2 hn.1.1
    apply div_lt_iff₀ (by simp; grind)|>.mpr
    rw [Nat.floor_lt <| div_nonneg (by linarith) (by linarith)] at this
    have := div_lt_iff₀ (by linarith)|>.mp this
    rwa [mul_comm] at this
  · exact E_nu_bound _ (div_nonneg hx.le (by simp))|>.1

noncomputable def a : ℝ := - ν.sum (fun m w ↦ w * log m / m)

lemma a_simpl : a = (7/15) * Real.log 2 + (3/10) * Real.log 3 + (1/6) * Real.log 5 := by
  norm_num [a, Finsupp.sum, single_apply, ν_support]
  norm_num [Finset.sum, ν]
  grind [show (30 : ℝ) = 2 * 3 * 5 by ring, log_mul, log_mul]

theorem a_bound : a ∈ Set.Icc 0.9212 0.9214 := by
  norm_num [Chebyshev.a_simpl]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, log3_bounds.1, log3_bounds.2, log5_bounds.1, log5_bounds.2]

noncomputable def e (x : ℝ) : ℝ :=
  (T x - (x * log x - x + 1))

lemma U_bound.lemma_1 (x : ℝ) : T x = x * log x - x + 1 + (e x) := by
  unfold e
  ring

lemma U_bound.lemma_2 (x : ℝ) (hx : 1 ≤ x) : |e x| ≤ log x := by
  rw [abs_le]
  unfold e
  constructor <;> linarith [T.ge x hx, T.le x hx]

lemma U_bound.lemma_3 (x : ℝ) :
    U x = ν.sum (fun m w ↦ w * ((x / m) * (log (x / m))))
          - ν.sum (fun m w ↦ w * (x / m))
          + ν.sum (fun _m w ↦ w)
          + ν.sum (fun m w ↦ w * e (x / m)) := by
  simp [U, Finsupp.sum, U_bound.lemma_1, sub_eq_add_neg, add_mul, mul_comm, sum_add_distrib]

lemma U_bound.lemma_4 (x : ℝ) (hx : 0 < x) :
    ν.sum (fun m w ↦ w * ((x / m) * log (x / m))) = a * x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : a = -(log 1 / 1 - log 2 / 2 - log 3 / 3 - log 5 / 5 + log 30 / 30) := by
    simp_rw [a, mul_div_assoc]; rw [ν_sum_mul (fun m ↦ log m / m)]; push_cast; rfl
  rw [ν_sum_mul (fun m ↦ (x / m) * log (x / m)), ha]
  simp [Real.log_div hx0]
  ring

lemma U_bound.lemma_5 (x : ℝ) : ν.sum (fun m w ↦ w * (x / m)) = 0 := by
  rw [ν_sum_mul (fun m ↦ x / m)]; push_cast; ring

lemma U_bound.lemma_6 : ν.sum (fun _ w ↦ w) = (-1 : ℝ) := by
  have := ν_sum_mul (fun _ ↦ (1 : ℝ)); simp at this; linarith

lemma Finsupp.abs_sum_le (A : Type*) (ν : A →₀ ℝ) (g : A → ℝ → ℝ) : |ν.sum g| ≤ ν.sum |g| := by
  simp_rw [Finsupp.sum.eq_1]
  exact abs_sum_le_sum_abs (fun i ↦ g i (ν i)) ν.support

theorem U_bound (x : ℝ) (hx : 30 ≤ x) : |U x - a * x| ≤ 5 * log x - 5 := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  rw [U_bound.lemma_3, U_bound.lemma_4 x hxpos]
  ring_nf
  have hlin : ν.sum (fun m w ↦ x * w * (↑m)⁻¹) = 0 :=
    by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm] using U_bound.lemma_5 x
  rw [hlin]; ring_nf; rw [U_bound.lemma_6]
  grw [abs_add_le, Finsupp.abs_sum_le]
  norm_num
  have hsupp_eq : ν.support = {1, 2, 3, 5, 30} := ν_support
  have hmem_of_supp : ∀ i ∈ ν.support, 0 < i ∧ i ≤ 30 := fun i hi ↦ by
    have : i ∈ ({1, 2, 3, 5, 30} : Finset ℕ) := hsupp_eq ▸ hi
    simp only [mem_insert, mem_singleton] at this
    constructor <;> omega
  have h : ν.sum |fun m w ↦ w * e (x * (↑m)⁻¹)| ≤ ν.sum (fun m w ↦ |w| * log (x * (↑m)⁻¹)) := by
    apply Finsupp.sum_le_sum
    intro i hi
    simp only [Pi.abs_apply, abs_mul]
    obtain ⟨hi_pos, hi_le⟩ := hmem_of_supp i hi
    have hxi : 1 ≤ x * (↑i)⁻¹ := by
      rw [le_mul_inv_iff₀ (by exact_mod_cast hi_pos)]
      linarith [show (i : ℝ) ≤ 30 from by exact_mod_cast hi_le]
    gcongr; exact U_bound.lemma_2 _ hxi
  grw [h]
  have hlog_split : ν.sum (fun m w ↦ |w| * log (x * (m : ℝ)⁻¹)) =
      log x * ν.sum (fun m w ↦ |w|) - ν.sum (fun m w ↦ |w| * log (↑m : ℝ)) := by
    simp only [Finsupp.sum]
    conv_rhs => rw [Finset.mul_sum, ← sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast (hmem_of_supp m hm).1
    rw [← div_eq_mul_inv, Real.log_div (ne_of_gt hxpos) (ne_of_gt hm_pos)]; ring
  rw [hlog_split]
  -- Once the support of `ν` is known explicitly, both `habs` and `hsum_eq`
  -- reduce to concrete arithmetic over a five-element finset.
  have expand_sum : ∀ f : ℕ → ℝ → ℝ, (∀ n, f n 0 = 0) →
      ν.sum f = f 1 1 + f 2 (-1) + f 3 (-1) + f 5 (-1) + f 30 1 := by
    intro f hf
    rw [Finsupp.sum_of_support_subset _ hsupp_eq.le _ (by intros; simp [hf])]
    simp only [sum_insert (by decide : (1:ℕ) ∉ ({2,3,5,30} : Finset ℕ)),
               sum_insert (by decide : (2:ℕ) ∉ ({3,5,30} : Finset ℕ)),
               sum_insert (by decide : (3:ℕ) ∉ ({5,30} : Finset ℕ)),
               sum_insert (by decide : (5:ℕ) ∉ ({30} : Finset ℕ)),
               sum_singleton, ν, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    ring
  have habs : ν.sum (fun m w ↦ |w|) = 5 := by
    rw [expand_sum _ (by intros; simp)]; norm_num
  have hgeq6 : ν.sum (fun m w ↦ |w| * log m) ≥ 6 := by
    have hsum_eq : ν.sum (fun m w ↦ |w| * log (m : ℝ)) = log 2 + log 3 + log 5 + log 30 := by
      rw [expand_sum _ (by intros; simp)]
      simp [log_one]
    have h30 : Real.log 30 = Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [show (30 : ℝ) = 2 * 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, log3_bounds.1, log5_bounds.1]
  grw [hgeq6]; rw [habs]; linarith

theorem psi_lower (x : ℝ) (hx : 30 ≤ x) : ψ x ≥ a * x - 5 * log x + 5 := by
  have h2 := abs_sub_le_iff.mp (U_bound x hx)
  linarith [psi_ge_weighted x (by linarith), h2.1]

end Chebyshev


open Finset Real

namespace P27
noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ)-1)/((p : ℝ)-2) else 1
noncomputable def Qs : Finset ℕ :=
  Classical.choose OAI.OddGoldbach23.finite_sieve_certificate
theorem Qs_card : Qs.card = 1000 :=
  (Classical.choose_spec OAI.OddGoldbach23.finite_sieve_certificate).1
theorem Qs_prop (p : ℕ) (hp : p ∈ Qs) : p.Prime ∧ p ≠ 2 ∧ p ≤ 7927 :=
  (Classical.choose_spec OAI.OddGoldbach23.finite_sieve_certificate).2.1 p hp
theorem T_bound : ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a-b) else 0) ≤ (867861 : ℝ) :=
  (Classical.choose_spec OAI.OddGoldbach23.finite_sieve_certificate).2.2
end P27

-- ===== RV =====
/-! Riesel–Vaughan small shifts: representations `s = a + q` with `a ∈ Q`, `q` an odd prime. -/

open Finset Real

namespace P27
open Schnir

/-- odd primes `≤ t`. -/
def oddP (t : ℕ) : Finset ℕ := (range (t + 1)).filter (fun p => p.Prime ∧ p ≠ 2)

theorem oddP_card (M : ℕ) (hM : 2 ≤ M) : (oddP M).card + 1 = Nat.primeCounting M := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have : oddP M = ((Finset.range (M + 1)).filter Nat.Prime).erase 2 := by
    ext p; simp [oddP, Finset.mem_erase]; tauto
  rw [this, Finset.card_erase_add_one]
  simp [Nat.prime_two]; omega

/-- `[s = a + q]` with `q` an odd prime. -/
noncomputable def ind (a s : ℕ) : ℕ := if a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2 then 1 else 0

/-- number of `a ∈ Q` with `s - a` an odd prime. -/
noncomputable def Rr (s : ℕ) : ℕ := #{a ∈ Qs | a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2}

theorem Rr_eq (s : ℕ) : Rr s = ∑ a ∈ Qs, ind a s := by
  rw [Rr, card_filter]; rfl

theorem ind_sq (a s : ℕ) : ind a s * ind a s = ind a s := by
  unfold ind; split_ifs <;> simp

theorem ind_mul (a b s : ℕ) : ind a s * ind b s =
    if (a ≤ s ∧ (s - a).Prime ∧ s - a ≠ 2) ∧ (b ≤ s ∧ (s - b).Prime ∧ s - b ≠ 2) then 1 else 0 := by
  unfold ind; rw [ite_zero_mul_ite_zero, one_mul]

/-- prime pairs `m, m + d` with `m + d ≤ x` (the count in Siebert's bound). -/
noncomputable def PPs (d x : ℕ) : ℕ := #{m ∈ range (x + 1) | m.Prime ∧ (m + d).Prime ∧ m + d ≤ x}

/-- first moment: each `a ∈ Q` contributes at least the odd primes up to `n - 7927`. -/
theorem sumR_lower (n : ℕ) (hn : 7929 ≤ n) :
    1000 * (oddP (n - 7927)).card ≤ ∑ s ∈ range (n + 1), Rr s := by
  simp_rw [Rr_eq]
  rw [sum_comm]
  have h : ∀ a ∈ Qs, (oddP (n - 7927)).card ≤ ∑ s ∈ range (n + 1), ind a s := by
    intro a ha
    obtain ⟨-, -, ha7927⟩ := Qs_prop a ha
    unfold ind
    rw [← card_filter]
    apply card_le_card_of_injOn (fun q => q + a)
    · intro q hq
      simp only [oddP, coe_filter, mem_range, Set.mem_ofPred_eq] at hq
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, Nat.add_sub_cancel]
      exact ⟨by omega, by omega, hq.2.1, hq.2.2⟩
    · intro q _ q' _ h
      simp only at h
      omega
  calc 1000 * (oddP (n - 7927)).card = ∑ _a ∈ Qs, (oddP (n - 7927)).card := by
        rw [sum_const, Qs_card, smul_eq_mul]
    _ ≤ _ := sum_le_sum h

/-- a pair `b < a` of shifts hits a prime pair `(s - a, s - b)`. -/
theorem pair_le (a b n : ℕ) (hba : b < a) :
    ∑ s ∈ range (n + 1), ind a s * ind b s ≤ PPs (a - b) n := by
  simp_rw [ind_mul]
  rw [← card_filter, PPs]
  apply card_le_card_of_injOn (fun s => s - a)
  · intro s hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    obtain ⟨hs, ⟨has, hpa, -⟩, ⟨hbs, hpb, -⟩⟩ := hs
    refine ⟨by omega, hpa, ?_, by omega⟩
    rwa [show s - a + (a - b) = s - b by omega]
  · intro s hs t ht h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs ht
    simp only at h
    omega

/-- pointwise square expansion. -/
theorem Rr_sq (s : ℕ) : Rr s ^ 2 = Rr s +
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then ind a s * ind b s else 0 := by
  have hsplit : ∀ a b : ℕ, ind a s * ind b s = (if b < a then ind a s * ind b s else 0) +
      (if a = b then ind a s else 0) + (if a < b then ind a s * ind b s else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.2 h.le]
    · subst h; simp [ind_sq]
    · simp [h, h.ne', not_lt.2 h.le]
  have hsym : (∑ a ∈ Qs, ∑ b ∈ Qs, if a < b then ind a s * ind b s else 0) =
      ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then ind a s * ind b s else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have hdiag : (∑ a ∈ Qs, ∑ b ∈ Qs, if a = b then ind a s else 0) = ∑ a ∈ Qs, ind a s :=
    sum_congr rfl fun a ha => by simp [ha]
  rw [Rr_eq, sq, sum_mul_sum]
  rw [sum_congr rfl fun a _ => sum_congr rfl fun b _ => hsplit a b]
  simp only [sum_add_distrib]
  rw [hsym, hdiag]
  ring

/-- second moment: diagonal plus prime pairs. -/
theorem sumR2_le (n : ℕ) : ∑ s ∈ range (n + 1), Rr s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr s +
    2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 := by
  simp_rw [Rr_sq]
  rw [sum_add_distrib, ← mul_sum]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  rw [sum_comm]
  refine sum_le_sum fun b _ => ?_
  split_ifs with h
  · exact pair_le a b n h
  · simp

theorem r_pos_of_Rr (s : ℕ) (h : Rr s ≠ 0) : 0 < r s := by
  rw [Rr] at h
  obtain ⟨a, ha⟩ := card_pos.1 (Nat.pos_of_ne_zero h)
  rw [mem_filter] at ha
  obtain ⟨haQ, has, hp, h2⟩ := ha
  obtain ⟨hap, ha2, -⟩ := Qs_prop a haQ
  unfold r
  exact card_pos.2 ⟨a, mem_filter.2 ⟨mem_range.2 (by omega), hap, ha2, hp, h2⟩⟩

/-- Cauchy–Schwarz. -/
theorem rv_cs (n : ℕ) : (∑ s ∈ range (n + 1), Rr s) ^ 2 ≤
    #{s ∈ range (n + 1) | 0 < r s} * ∑ s ∈ range (n + 1), Rr s ^ 2 := by
  set F := (range (n + 1)).filter (fun s => Rr s ≠ 0) with hF
  have h1 : ∑ s ∈ range (n + 1), Rr s = ∑ s ∈ F, Rr s := (sum_filter_ne_zero _).symm
  have h2 : ∑ s ∈ F, Rr s ^ 2 ≤ ∑ s ∈ range (n + 1), Rr s ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : #F ≤ #{s ∈ range (n + 1) | 0 < r s} := by
    apply card_le_card
    intro s hs
    rw [hF, mem_filter] at hs
    exact mem_filter.2 ⟨hs.1, r_pos_of_Rr s hs.2⟩
  rw [h1]
  calc (∑ s ∈ F, Rr s) ^ 2 ≤ #F * ∑ s ∈ F, Rr s ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := Nat.mul_le_mul h3 h2


end P27

-- ===== RVPiece =====
/-! The analytic inequalities for one piece `La ≤ log n ≤ Lb` of the middle range. -/

open Finset Real

namespace P27
open Schnir

theorem exp99_ge (x : ℝ) (hx : 70 ≤ x) : (10 : ℝ) ^ 8 ≤ exp x := by
  have h3 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
  have h : exp 70 = exp 2 ^ 35 := by rw [← exp_nat_mul]; norm_num
  calc (10 : ℝ) ^ 8 ≤ 3 ^ 35 := by norm_num
    _ ≤ exp 2 ^ 35 := pow_le_pow_left₀ (by norm_num) h3 35
    _ = exp 70 := h.symm
    _ ≤ exp x := exp_le_exp.2 hx

/-- first moment, from Chebyshev's `ψ(m) ≥ a m - 5 log m + 5` (`a ≥ 0.9212`). -/
theorem X_lower (n : ℕ) (Lb : ℝ) (hn : (10 : ℝ) ^ 8 ≤ n) (hLb : log n ≤ Lb) (hLb12 : Lb ≤ 300) :
    1000 * 0.9719 / Lb * n ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
  have hn7929 : 7929 ≤ n := by exact_mod_cast (show (7929 : ℝ) ≤ n by linarith)
  set m := n - 7927 with hm
  have hmR : (m : ℝ) = n - 7927 := by rw [hm, Nat.cast_sub (by omega)]; norm_num
  have hX := sumR_lower n hn7929
  have hP := oddP_card m (by omega)
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  have hlogm : log m ≤ log n := log_le_log hm0 (by rw [hmR]; linarith)
  have hlogm0 : 0 < log (m : ℝ) := log_pos (by rw [hmR]; linarith)
  have hc : ((oddP m).card : ℝ) + 1 = Nat.primeCounting m := by exact_mod_cast hP
  have e1 : ((oddP m).card : ℝ) * log m = (Nat.primeCounting m : ℝ) * log m - log m := by
    rw [← hc]; ring
  have hm1340 : 1340 ≤ m := by exact_mod_cast (show (1340 : ℝ) ≤ m by rw [hmR]; linarith)
  have hm18 : 18 ≤ log (m : ℝ) := by
    apply (le_log_iff_exp_le hm0).2
    have hexp : exp 18 = exp 1 ^ 18 := by rw [← exp_nat_mul]; norm_num
    rw [hexp]
    have hb : exp 1 ≤ (2.72 : ℝ) := by linarith [exp_one_lt_d9]
    have hpow := pow_le_pow_left₀ (exp_pos 1).le hb 18
    have hnume : (2.72 : ℝ)^18 ≤ 10^8-7927 := by norm_num
    rw [hmR]
    linarith
  have hpi := OddGoldbach21.primeCounting_lower18 m hm1340 hm18
  have hpi' : (0.972 : ℝ) * m ≤ (Nat.primeCounting m : ℝ) * log m :=
    (div_le_iff₀ hlogm0).1 hpi
  have key : (0.972 : ℝ) * m - log m ≤ ((oddP m).card : ℝ) * log m := by
    rw [e1]; linarith
  have hcard0 : (0 : ℝ) ≤ (oddP m).card := Nat.cast_nonneg _
  have hk2 : ((oddP m).card : ℝ) * log m ≤ ((oddP m).card : ℝ) * Lb :=
    mul_le_mul_of_nonneg_left (hlogm.trans hLb) hcard0
  have hlogm12 : log (m : ℝ) ≤ 300 := hlogm.trans (hLb.trans hLb12)
  have hmain : 0.9719 * (n : ℝ) ≤ ((oddP m).card : ℝ) * Lb := by
    linarith
  have hLbpos : 0 < Lb := lt_of_lt_of_le (log_pos (by linarith)) hLb
  have hXc : (1000 : ℝ) * (oddP m).card ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
    exact_mod_cast hX
  rw [div_mul_eq_mul_div, div_le_iff₀ hLbpos]
  have := mul_le_mul_of_nonneg_right hXc hLbpos.le
  linarith

/-- Siebert's bound for one shift. -/
theorem PPs_le (d n : ℕ) (hn : 2 ≤ n) (hd0 : 0 < d) (hd2 : 2 ∣ d) :
    (PPs d n : ℝ) ≤ 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 * Kf d := by
  have h := TaoFivePrimes.siebert_prime_pair_bound n d hn hd0 hd2
  have e : (PPs d n : ℝ) = ∑ m ∈ range (n + 1),
      if Nat.Prime m ∧ Nat.Prime (m + d) ∧ m + d ≤ n then (1 : ℝ) else 0 := by
    rw [PPs, Finset.natCast_card_filter]
  rw [e]
  exact h

/-- the off-diagonal (prime pair) part of the second moment. -/
theorem off_le (n : ℕ) (La : ℝ) (hLa : 19 ≤ La) (h1 : La ≤ log n) :
    ((2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      n * (16 * 1.3217 * 867861 / La ^ 2) := by
  obtain ⟨-, hCup, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  have hC0 : 0 ≤ TaoFivePrimes.twinPrimeConstant := by
    obtain ⟨h, -⟩ := PrimePairSieve.sieve_constants_certificate; linarith
  have hL : 19 ≤ log (n : ℝ) := hLa.trans h1
  have hnpos : (0 : ℝ) < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hL; simp at hL; linarith
    · exact_mod_cast h
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have : (n : ℝ) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
    have := log_le_log hnpos this
    rw [log_one] at this; linarith
  set w := 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      w * (if b < a then Kf (a - b) else 0) := by
    intro a ha b hb
    obtain ⟨hap, ha2, -⟩ := Qs_prop a ha
    obtain ⟨hbp, hb2, -⟩ := Qs_prop b hb
    split_ifs with hab
    · have hao := hap.odd_of_ne_two ha2
      have hbo := hbp.odd_of_ne_two hb2
      have hev : 2 ∣ a - b := by
        obtain ⟨i, hi⟩ := hao; obtain ⟨j, hj⟩ := hbo
        exact ⟨i - j, by omega⟩
      exact PPs_le (a - b) n hn2 (by omega) hev
    · simp
  have hsum : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      w * 867861 := by
    have hcast : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) =
        ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
    rw [hcast]
    calc ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ)
        ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, w * (if b < a then Kf (a - b) else 0) :=
          sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
      _ = w * ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) := by
          rw [mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
      _ ≤ w * 867861 := mul_le_mul_of_nonneg_left T_bound hw0
  have hwle : w ≤ 8 * 1.3217 * n / La ^ 2 := by
    rw [hw]
    have hLa2 : La ^ 2 ≤ (log n) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    calc 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 ≤ 8 * 1.3217 * n / (log n) ^ 2 := by
          gcongr
      _ ≤ 8 * 1.3217 * n / La ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hLa2
  push_cast at hsum ⊢
  have : 2 * (w * 867861) ≤ n * (16 * 1.3217 * 867861 / La ^ 2) := by
    have e : (n : ℝ) * (16 * 1.3217 * 867861 / La ^ 2) = 2 * (8 * 1.3217 * n / La ^ 2 * 867861) := by ring
    rw [e]; nlinarith
  linarith

/-- one piece of the middle range: `#{s ≤ n : r(s) > 0} ≥ n * (100 / 1999)`. -/
theorem rv_piece (n : ℕ) (La Lb : ℝ) (hLa : 19 ≤ La) (hLb12 : Lb ≤ 300)
    (h1 : La ≤ log n) (h2 : log n ≤ Lb) (hxb : 1 * (50 / 1999) ≤ 1000 * 0.9719 / Lb)
    (hnum : 1000 * 0.9719 / Lb + 16 * 1.3217 * 867861 / La ^ 2 ≤ 19.99 * (1000 * 0.9719 / Lb) ^ 2) :
    (n : ℝ) * (100 / 1999) ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  have hn12 : (10 : ℝ) ^ 8 ≤ n := by
    have hnpos : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at h1; simp at h1; linarith
      · exact_mod_cast h
    rw [← exp_log hnpos]
    have h3 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have : (10 : ℝ) ^ 8 ≤ exp 19 := by
      have e : exp 19 = exp 1 ^ 19 := by rw [← exp_nat_mul]; norm_num
      rw [e]
      calc (10 : ℝ) ^ 8 ≤ 2.7 ^ 19 := by norm_num
        _ ≤ exp 1 ^ 19 := pow_le_pow_left₀ (by norm_num) h3 19
    exact this.trans (exp_le_exp.2 (by linarith))
  set x := 1000 * 0.9719 / Lb with hx
  set k := 16 * 1.3217 * 867861 / La ^ 2 with hk
  have hX := X_lower n Lb hn12 h2 hLb12
  have hoff := off_le n La hLa h1
  have hcs := rv_cs n
  have h2m := sumR2_le n
  set X := ∑ s ∈ range (n + 1), Rr s with hXdef
  set off := 2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 with hoffdef
  set cnt := #{s ∈ range (n + 1) | 0 < r s} with hcnt
  have hcsN : X ^ 2 ≤ cnt * (X + off) := hcs.trans (Nat.mul_le_mul_left _ h2m)
  have hcsR : (X : ℝ) ^ 2 ≤ cnt * (X + off) := by exact_mod_cast hcsN
  have hX' : (n : ℝ) * x ≤ X := by rw [hx, mul_comm]; exact hX
  have hoff' : (off : ℝ) ≤ n * k := by rw [hk]; exact hoff
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ cnt := Nat.cast_nonneg _
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  by_contra hcon
  push Not at hcon
  have hnpos : (0 : ℝ) < n := by linarith
  have hxpos : 0 < x := by linarith
  have hXpos : 0 < (X : ℝ) := lt_of_lt_of_le (mul_pos hnpos hxpos) hX'
  have hnk : 0 ≤ (n : ℝ) * k := mul_nonneg hn0 hk0
  have h3 : (cnt : ℝ) * (X + off) ≤ cnt * (X + n * k) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have h4 : (cnt : ℝ) * (X + n * k) < n * (100 / 1999) * (X + n * k) :=
    mul_lt_mul_of_pos_right hcon (by linarith)
  have p1 : 0 ≤ ((X : ℝ) - n * x) * (X + n * x - n * (100 / 1999)) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (n : ℝ) * (2 * x - 1 * (100 / 1999)) := mul_nonneg hn0 (by linarith)
    linarith
  have p2 : 0 ≤ (n : ℝ) ^ 2 * (19.99 * x ^ 2 - x - k) := mul_nonneg (sq_nonneg _) (by linarith)
  have e : (X : ℝ) ^ 2 - n * (100 / 1999) * (X + n * k) =
      ((X : ℝ) - n * x) * (X + n * x - n * (100 / 1999)) + (n : ℝ) ^ 2 * (19.99 * x ^ 2 - x - k) * (100 / 1999) := by
    ring
  linarith

end P27

-- ===== RVRange =====
/-! The middle range `19 ≤ log n ≤ 300`, split into pieces. -/

open Finset Real

namespace P27
open Schnir

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem rv_range (n : ℕ) (h1 : 19 ≤ log n) (h2 : log n ≤ 300) :
    (n : ℝ) * (100 / 1999) ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  rcases le_or_gt (log (n : ℝ)) (191/10) with hbpre190 | hpre190
  · exact rv_piece n (190/10) (191/10) (by norm_num) (by norm_num) (by convert h1 using 1 <;> norm_num) hbpre190 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (192/10) with hbpre191 | hpre191
  · exact rv_piece n (191/10) (192/10) (by norm_num) (by norm_num) hpre190.le hbpre191 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (193/10) with hbpre192 | hpre192
  · exact rv_piece n (192/10) (193/10) (by norm_num) (by norm_num) hpre191.le hbpre192 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (194/10) with hbpre193 | hpre193
  · exact rv_piece n (193/10) (194/10) (by norm_num) (by norm_num) hpre192.le hbpre193 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (195/10) with hbpre194 | hpre194
  · exact rv_piece n (194/10) (195/10) (by norm_num) (by norm_num) hpre193.le hbpre194 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (196/10) with hbpre195 | hpre195
  · exact rv_piece n (195/10) (196/10) (by norm_num) (by norm_num) hpre194.le hbpre195 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (197/10) with hbpre196 | hpre196
  · exact rv_piece n (196/10) (197/10) (by norm_num) (by norm_num) hpre195.le hbpre196 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (198/10) with hbpre197 | hpre197
  · exact rv_piece n (197/10) (198/10) (by norm_num) (by norm_num) hpre196.le hbpre197 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (199/10) with hbpre198 | hpre198
  · exact rv_piece n (198/10) (199/10) (by norm_num) (by norm_num) hpre197.le hbpre198 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (200/10) with hbpre199 | hpre199
  · exact rv_piece n (199/10) (200/10) (by norm_num) (by norm_num) hpre198.le hbpre199 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (201/10) with hb200 | ha200
  · exact rv_piece n (200/10) (201/10) (by norm_num) (by norm_num) (by convert hpre199.le using 1 <;> norm_num) hb200 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (202/10) with hb201 | ha201
  · exact rv_piece n (201/10) (202/10) (by norm_num) (by norm_num) ha200.le hb201 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (203/10) with hb202 | ha202
  · exact rv_piece n (202/10) (203/10) (by norm_num) (by norm_num) ha201.le hb202 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (204/10) with hb203 | ha203
  · exact rv_piece n (203/10) (204/10) (by norm_num) (by norm_num) ha202.le hb203 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (205/10) with hb204 | ha204
  · exact rv_piece n (204/10) (205/10) (by norm_num) (by norm_num) ha203.le hb204 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (206/10) with hb205 | ha205
  · exact rv_piece n (205/10) (206/10) (by norm_num) (by norm_num) ha204.le hb205 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (207/10) with hb206 | ha206
  · exact rv_piece n (206/10) (207/10) (by norm_num) (by norm_num) ha205.le hb206 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (208/10) with hb207 | ha207
  · exact rv_piece n (207/10) (208/10) (by norm_num) (by norm_num) ha206.le hb207 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (209/10) with hb208 | ha208
  · exact rv_piece n (208/10) (209/10) (by norm_num) (by norm_num) ha207.le hb208 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (210/10) with hb209 | ha209
  · exact rv_piece n (209/10) (210/10) (by norm_num) (by norm_num) ha208.le hb209 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (211/10) with hb210 | ha210
  · exact rv_piece n (210/10) (211/10) (by norm_num) (by norm_num) ha209.le hb210 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (212/10) with hb211 | ha211
  · exact rv_piece n (211/10) (212/10) (by norm_num) (by norm_num) ha210.le hb211 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (213/10) with hb212 | ha212
  · exact rv_piece n (212/10) (213/10) (by norm_num) (by norm_num) ha211.le hb212 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (214/10) with hb213 | ha213
  · exact rv_piece n (213/10) (214/10) (by norm_num) (by norm_num) ha212.le hb213 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (215/10) with hb214 | ha214
  · exact rv_piece n (214/10) (215/10) (by norm_num) (by norm_num) ha213.le hb214 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (216/10) with hb215 | ha215
  · exact rv_piece n (215/10) (216/10) (by norm_num) (by norm_num) ha214.le hb215 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (217/10) with hb216 | ha216
  · exact rv_piece n (216/10) (217/10) (by norm_num) (by norm_num) ha215.le hb216 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (218/10) with hb217 | ha217
  · exact rv_piece n (217/10) (218/10) (by norm_num) (by norm_num) ha216.le hb217 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (219/10) with hb218 | ha218
  · exact rv_piece n (218/10) (219/10) (by norm_num) (by norm_num) ha217.le hb218 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (220/10) with hb219 | ha219
  · exact rv_piece n (219/10) (220/10) (by norm_num) (by norm_num) ha218.le hb219 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (221/10) with hb220 | ha220
  · exact rv_piece n (220/10) (221/10) (by norm_num) (by norm_num) ha219.le hb220 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (222/10) with hb221 | ha221
  · exact rv_piece n (221/10) (222/10) (by norm_num) (by norm_num) ha220.le hb221 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (223/10) with hb222 | ha222
  · exact rv_piece n (222/10) (223/10) (by norm_num) (by norm_num) ha221.le hb222 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (224/10) with hb223 | ha223
  · exact rv_piece n (223/10) (224/10) (by norm_num) (by norm_num) ha222.le hb223 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (225/10) with hb224 | ha224
  · exact rv_piece n (224/10) (225/10) (by norm_num) (by norm_num) ha223.le hb224 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (226/10) with hb225 | ha225
  · exact rv_piece n (225/10) (226/10) (by norm_num) (by norm_num) ha224.le hb225 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (227/10) with hb226 | ha226
  · exact rv_piece n (226/10) (227/10) (by norm_num) (by norm_num) ha225.le hb226 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (228/10) with hb227 | ha227
  · exact rv_piece n (227/10) (228/10) (by norm_num) (by norm_num) ha226.le hb227 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (229/10) with hb228 | ha228
  · exact rv_piece n (228/10) (229/10) (by norm_num) (by norm_num) ha227.le hb228 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (230/10) with hb229 | ha229
  · exact rv_piece n (229/10) (230/10) (by norm_num) (by norm_num) ha228.le hb229 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (231/10) with hb230 | ha230
  · exact rv_piece n (230/10) (231/10) (by norm_num) (by norm_num) ha229.le hb230 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (232/10) with hb231 | ha231
  · exact rv_piece n (231/10) (232/10) (by norm_num) (by norm_num) ha230.le hb231 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (233/10) with hb232 | ha232
  · exact rv_piece n (232/10) (233/10) (by norm_num) (by norm_num) ha231.le hb232 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (234/10) with hb233 | ha233
  · exact rv_piece n (233/10) (234/10) (by norm_num) (by norm_num) ha232.le hb233 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (235/10) with hb234 | ha234
  · exact rv_piece n (234/10) (235/10) (by norm_num) (by norm_num) ha233.le hb234 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (236/10) with hb235 | ha235
  · exact rv_piece n (235/10) (236/10) (by norm_num) (by norm_num) ha234.le hb235 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (237/10) with hb236 | ha236
  · exact rv_piece n (236/10) (237/10) (by norm_num) (by norm_num) ha235.le hb236 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (238/10) with hb237 | ha237
  · exact rv_piece n (237/10) (238/10) (by norm_num) (by norm_num) ha236.le hb237 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (239/10) with hb238 | ha238
  · exact rv_piece n (238/10) (239/10) (by norm_num) (by norm_num) ha237.le hb238 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (240/10) with hb239 | ha239
  · exact rv_piece n (239/10) (240/10) (by norm_num) (by norm_num) ha238.le hb239 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (241/10) with hb240 | ha240
  · exact rv_piece n (240/10) (241/10) (by norm_num) (by norm_num) ha239.le hb240 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (242/10) with hb241 | ha241
  · exact rv_piece n (241/10) (242/10) (by norm_num) (by norm_num) ha240.le hb241 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (243/10) with hb242 | ha242
  · exact rv_piece n (242/10) (243/10) (by norm_num) (by norm_num) ha241.le hb242 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (244/10) with hb243 | ha243
  · exact rv_piece n (243/10) (244/10) (by norm_num) (by norm_num) ha242.le hb243 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (245/10) with hb244 | ha244
  · exact rv_piece n (244/10) (245/10) (by norm_num) (by norm_num) ha243.le hb244 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (246/10) with hb245 | ha245
  · exact rv_piece n (245/10) (246/10) (by norm_num) (by norm_num) ha244.le hb245 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (247/10) with hb246 | ha246
  · exact rv_piece n (246/10) (247/10) (by norm_num) (by norm_num) ha245.le hb246 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (248/10) with hb247 | ha247
  · exact rv_piece n (247/10) (248/10) (by norm_num) (by norm_num) ha246.le hb247 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (249/10) with hb248 | ha248
  · exact rv_piece n (248/10) (249/10) (by norm_num) (by norm_num) ha247.le hb248 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (250/10) with hb249 | ha249
  · exact rv_piece n (249/10) (250/10) (by norm_num) (by norm_num) ha248.le hb249 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (251/10) with hb250 | ha250
  · exact rv_piece n (250/10) (251/10) (by norm_num) (by norm_num) ha249.le hb250 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (252/10) with hb251 | ha251
  · exact rv_piece n (251/10) (252/10) (by norm_num) (by norm_num) ha250.le hb251 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (253/10) with hb252 | ha252
  · exact rv_piece n (252/10) (253/10) (by norm_num) (by norm_num) ha251.le hb252 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (254/10) with hb253 | ha253
  · exact rv_piece n (253/10) (254/10) (by norm_num) (by norm_num) ha252.le hb253 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (255/10) with hb254 | ha254
  · exact rv_piece n (254/10) (255/10) (by norm_num) (by norm_num) ha253.le hb254 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (256/10) with hb255 | ha255
  · exact rv_piece n (255/10) (256/10) (by norm_num) (by norm_num) ha254.le hb255 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (257/10) with hb256 | ha256
  · exact rv_piece n (256/10) (257/10) (by norm_num) (by norm_num) ha255.le hb256 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (258/10) with hb257 | ha257
  · exact rv_piece n (257/10) (258/10) (by norm_num) (by norm_num) ha256.le hb257 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (259/10) with hb258 | ha258
  · exact rv_piece n (258/10) (259/10) (by norm_num) (by norm_num) ha257.le hb258 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (260/10) with hb259 | ha259
  · exact rv_piece n (259/10) (260/10) (by norm_num) (by norm_num) ha258.le hb259 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (261/10) with hb260 | ha260
  · exact rv_piece n (260/10) (261/10) (by norm_num) (by norm_num) ha259.le hb260 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (262/10) with hb261 | ha261
  · exact rv_piece n (261/10) (262/10) (by norm_num) (by norm_num) ha260.le hb261 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (263/10) with hb262 | ha262
  · exact rv_piece n (262/10) (263/10) (by norm_num) (by norm_num) ha261.le hb262 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (264/10) with hb263 | ha263
  · exact rv_piece n (263/10) (264/10) (by norm_num) (by norm_num) ha262.le hb263 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (266/10) with hb264 | ha264
  · exact rv_piece n (264/10) (266/10) (by norm_num) (by norm_num) ha263.le hb264 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (268/10) with hb266 | ha266
  · exact rv_piece n (266/10) (268/10) (by norm_num) (by norm_num) ha264.le hb266 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (270/10) with hb268 | ha268
  · exact rv_piece n (268/10) (270/10) (by norm_num) (by norm_num) ha266.le hb268 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (272/10) with hb270 | ha270
  · exact rv_piece n (270/10) (272/10) (by norm_num) (by norm_num) ha268.le hb270 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (274/10) with hb272 | ha272
  · exact rv_piece n (272/10) (274/10) (by norm_num) (by norm_num) ha270.le hb272 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (276/10) with hb274 | ha274
  · exact rv_piece n (274/10) (276/10) (by norm_num) (by norm_num) ha272.le hb274 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (278/10) with hb276 | ha276
  · exact rv_piece n (276/10) (278/10) (by norm_num) (by norm_num) ha274.le hb276 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (280/10) with hb278 | ha278
  · exact rv_piece n (278/10) (280/10) (by norm_num) (by norm_num) ha276.le hb278 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (282/10) with hb280 | ha280
  · exact rv_piece n (280/10) (282/10) (by norm_num) (by norm_num) ha278.le hb280 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (284/10) with hb282 | ha282
  · exact rv_piece n (282/10) (284/10) (by norm_num) (by norm_num) ha280.le hb282 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (286/10) with hb284 | ha284
  · exact rv_piece n (284/10) (286/10) (by norm_num) (by norm_num) ha282.le hb284 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (288/10) with hb286 | ha286
  · exact rv_piece n (286/10) (288/10) (by norm_num) (by norm_num) ha284.le hb286 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (290/10) with hb288 | ha288
  · exact rv_piece n (288/10) (290/10) (by norm_num) (by norm_num) ha286.le hb288 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (292/10) with hb290 | ha290
  · exact rv_piece n (290/10) (292/10) (by norm_num) (by norm_num) ha288.le hb290 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (294/10) with hb292 | ha292
  · exact rv_piece n (292/10) (294/10) (by norm_num) (by norm_num) ha290.le hb292 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (296/10) with hb294 | ha294
  · exact rv_piece n (294/10) (296/10) (by norm_num) (by norm_num) ha292.le hb294 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (298/10) with hb296 | ha296
  · exact rv_piece n (296/10) (298/10) (by norm_num) (by norm_num) ha294.le hb296 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (300/10) with hb298 | ha298
  · exact rv_piece n (298/10) (300/10) (by norm_num) (by norm_num) ha296.le hb298 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (302/10) with hb300 | ha300
  · exact rv_piece n (300/10) (302/10) (by norm_num) (by norm_num) ha298.le hb300 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (304/10) with hb302 | ha302
  · exact rv_piece n (302/10) (304/10) (by norm_num) (by norm_num) ha300.le hb302 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (306/10) with hb304 | ha304
  · exact rv_piece n (304/10) (306/10) (by norm_num) (by norm_num) ha302.le hb304 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (308/10) with hb306 | ha306
  · exact rv_piece n (306/10) (308/10) (by norm_num) (by norm_num) ha304.le hb306 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (310/10) with hb308 | ha308
  · exact rv_piece n (308/10) (310/10) (by norm_num) (by norm_num) ha306.le hb308 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (312/10) with hb310 | ha310
  · exact rv_piece n (310/10) (312/10) (by norm_num) (by norm_num) ha308.le hb310 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (314/10) with hb312 | ha312
  · exact rv_piece n (312/10) (314/10) (by norm_num) (by norm_num) ha310.le hb312 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (316/10) with hb314 | ha314
  · exact rv_piece n (314/10) (316/10) (by norm_num) (by norm_num) ha312.le hb314 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (318/10) with hb316 | ha316
  · exact rv_piece n (316/10) (318/10) (by norm_num) (by norm_num) ha314.le hb316 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (320/10) with hb318 | ha318
  · exact rv_piece n (318/10) (320/10) (by norm_num) (by norm_num) ha316.le hb318 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (322/10) with hb320 | ha320
  · exact rv_piece n (320/10) (322/10) (by norm_num) (by norm_num) ha318.le hb320 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (324/10) with hb322 | ha322
  · exact rv_piece n (322/10) (324/10) (by norm_num) (by norm_num) ha320.le hb322 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (326/10) with hb324 | ha324
  · exact rv_piece n (324/10) (326/10) (by norm_num) (by norm_num) ha322.le hb324 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (328/10) with hb326 | ha326
  · exact rv_piece n (326/10) (328/10) (by norm_num) (by norm_num) ha324.le hb326 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (330/10) with hb328 | ha328
  · exact rv_piece n (328/10) (330/10) (by norm_num) (by norm_num) ha326.le hb328 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (332/10) with hb330 | ha330
  · exact rv_piece n (330/10) (332/10) (by norm_num) (by norm_num) ha328.le hb330 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (334/10) with hb332 | ha332
  · exact rv_piece n (332/10) (334/10) (by norm_num) (by norm_num) ha330.le hb332 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (336/10) with hb334 | ha334
  · exact rv_piece n (334/10) (336/10) (by norm_num) (by norm_num) ha332.le hb334 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (338/10) with hb336 | ha336
  · exact rv_piece n (336/10) (338/10) (by norm_num) (by norm_num) ha334.le hb336 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (340/10) with hb338 | ha338
  · exact rv_piece n (338/10) (340/10) (by norm_num) (by norm_num) ha336.le hb338 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (342/10) with hb340 | ha340
  · exact rv_piece n (340/10) (342/10) (by norm_num) (by norm_num) ha338.le hb340 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (344/10) with hb342 | ha342
  · exact rv_piece n (342/10) (344/10) (by norm_num) (by norm_num) ha340.le hb342 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (346/10) with hb344 | ha344
  · exact rv_piece n (344/10) (346/10) (by norm_num) (by norm_num) ha342.le hb344 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (348/10) with hb346 | ha346
  · exact rv_piece n (346/10) (348/10) (by norm_num) (by norm_num) ha344.le hb346 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (350/10) with hb348 | ha348
  · exact rv_piece n (348/10) (350/10) (by norm_num) (by norm_num) ha346.le hb348 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (352/10) with hb350 | ha350
  · exact rv_piece n (350/10) (352/10) (by norm_num) (by norm_num) ha348.le hb350 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (354/10) with hb352 | ha352
  · exact rv_piece n (352/10) (354/10) (by norm_num) (by norm_num) ha350.le hb352 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (356/10) with hb354 | ha354
  · exact rv_piece n (354/10) (356/10) (by norm_num) (by norm_num) ha352.le hb354 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (358/10) with hb356 | ha356
  · exact rv_piece n (356/10) (358/10) (by norm_num) (by norm_num) ha354.le hb356 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (360/10) with hb358 | ha358
  · exact rv_piece n (358/10) (360/10) (by norm_num) (by norm_num) ha356.le hb358 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (362/10) with hb360 | ha360
  · exact rv_piece n (360/10) (362/10) (by norm_num) (by norm_num) ha358.le hb360 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (364/10) with hb362 | ha362
  · exact rv_piece n (362/10) (364/10) (by norm_num) (by norm_num) ha360.le hb362 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (366/10) with hb364 | ha364
  · exact rv_piece n (364/10) (366/10) (by norm_num) (by norm_num) ha362.le hb364 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (368/10) with hb366 | ha366
  · exact rv_piece n (366/10) (368/10) (by norm_num) (by norm_num) ha364.le hb366 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (370/10) with hb368 | ha368
  · exact rv_piece n (368/10) (370/10) (by norm_num) (by norm_num) ha366.le hb368 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (372/10) with hb370 | ha370
  · exact rv_piece n (370/10) (372/10) (by norm_num) (by norm_num) ha368.le hb370 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (374/10) with hb372 | ha372
  · exact rv_piece n (372/10) (374/10) (by norm_num) (by norm_num) ha370.le hb372 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (376/10) with hb374 | ha374
  · exact rv_piece n (374/10) (376/10) (by norm_num) (by norm_num) ha372.le hb374 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (378/10) with hb376 | ha376
  · exact rv_piece n (376/10) (378/10) (by norm_num) (by norm_num) ha374.le hb376 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (380/10) with hb378 | ha378
  · exact rv_piece n (378/10) (380/10) (by norm_num) (by norm_num) ha376.le hb378 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (382/10) with hb380 | ha380
  · exact rv_piece n (380/10) (382/10) (by norm_num) (by norm_num) ha378.le hb380 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (384/10) with hb382 | ha382
  · exact rv_piece n (382/10) (384/10) (by norm_num) (by norm_num) ha380.le hb382 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (386/10) with hb384 | ha384
  · exact rv_piece n (384/10) (386/10) (by norm_num) (by norm_num) ha382.le hb384 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (388/10) with hb386 | ha386
  · exact rv_piece n (386/10) (388/10) (by norm_num) (by norm_num) ha384.le hb386 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (390/10) with hb388 | ha388
  · exact rv_piece n (388/10) (390/10) (by norm_num) (by norm_num) ha386.le hb388 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (392/10) with hb390 | ha390
  · exact rv_piece n (390/10) (392/10) (by norm_num) (by norm_num) ha388.le hb390 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (394/10) with hb392 | ha392
  · exact rv_piece n (392/10) (394/10) (by norm_num) (by norm_num) ha390.le hb392 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (396/10) with hb394 | ha394
  · exact rv_piece n (394/10) (396/10) (by norm_num) (by norm_num) ha392.le hb394 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (398/10) with hb396 | ha396
  · exact rv_piece n (396/10) (398/10) (by norm_num) (by norm_num) ha394.le hb396 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (400/10) with hb398 | ha398
  · exact rv_piece n (398/10) (400/10) (by norm_num) (by norm_num) ha396.le hb398 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (402/10) with hb400 | ha400
  · exact rv_piece n (400/10) (402/10) (by norm_num) (by norm_num) ha398.le hb400 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (404/10) with hb402 | ha402
  · exact rv_piece n (402/10) (404/10) (by norm_num) (by norm_num) ha400.le hb402 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (406/10) with hb404 | ha404
  · exact rv_piece n (404/10) (406/10) (by norm_num) (by norm_num) ha402.le hb404 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (408/10) with hb406 | ha406
  · exact rv_piece n (406/10) (408/10) (by norm_num) (by norm_num) ha404.le hb406 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (410/10) with hb408 | ha408
  · exact rv_piece n (408/10) (410/10) (by norm_num) (by norm_num) ha406.le hb408 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (412/10) with hb410 | ha410
  · exact rv_piece n (410/10) (412/10) (by norm_num) (by norm_num) ha408.le hb410 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (414/10) with hb412 | ha412
  · exact rv_piece n (412/10) (414/10) (by norm_num) (by norm_num) ha410.le hb412 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (416/10) with hb414 | ha414
  · exact rv_piece n (414/10) (416/10) (by norm_num) (by norm_num) ha412.le hb414 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (418/10) with hb416 | ha416
  · exact rv_piece n (416/10) (418/10) (by norm_num) (by norm_num) ha414.le hb416 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (421/10) with hb418 | ha418
  · exact rv_piece n (418/10) (421/10) (by norm_num) (by norm_num) ha416.le hb418 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (424/10) with hb421 | ha421
  · exact rv_piece n (421/10) (424/10) (by norm_num) (by norm_num) ha418.le hb421 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (427/10) with hb424 | ha424
  · exact rv_piece n (424/10) (427/10) (by norm_num) (by norm_num) ha421.le hb424 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (430/10) with hb427 | ha427
  · exact rv_piece n (427/10) (430/10) (by norm_num) (by norm_num) ha424.le hb427 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (433/10) with hb430 | ha430
  · exact rv_piece n (430/10) (433/10) (by norm_num) (by norm_num) ha427.le hb430 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (436/10) with hb433 | ha433
  · exact rv_piece n (433/10) (436/10) (by norm_num) (by norm_num) ha430.le hb433 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (439/10) with hb436 | ha436
  · exact rv_piece n (436/10) (439/10) (by norm_num) (by norm_num) ha433.le hb436 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (442/10) with hb439 | ha439
  · exact rv_piece n (439/10) (442/10) (by norm_num) (by norm_num) ha436.le hb439 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (445/10) with hb442 | ha442
  · exact rv_piece n (442/10) (445/10) (by norm_num) (by norm_num) ha439.le hb442 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (448/10) with hb445 | ha445
  · exact rv_piece n (445/10) (448/10) (by norm_num) (by norm_num) ha442.le hb445 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (451/10) with hb448 | ha448
  · exact rv_piece n (448/10) (451/10) (by norm_num) (by norm_num) ha445.le hb448 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (454/10) with hb451 | ha451
  · exact rv_piece n (451/10) (454/10) (by norm_num) (by norm_num) ha448.le hb451 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (457/10) with hb454 | ha454
  · exact rv_piece n (454/10) (457/10) (by norm_num) (by norm_num) ha451.le hb454 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (460/10) with hb457 | ha457
  · exact rv_piece n (457/10) (460/10) (by norm_num) (by norm_num) ha454.le hb457 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (463/10) with hb460 | ha460
  · exact rv_piece n (460/10) (463/10) (by norm_num) (by norm_num) ha457.le hb460 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (466/10) with hb463 | ha463
  · exact rv_piece n (463/10) (466/10) (by norm_num) (by norm_num) ha460.le hb463 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (469/10) with hb466 | ha466
  · exact rv_piece n (466/10) (469/10) (by norm_num) (by norm_num) ha463.le hb466 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (472/10) with hb469 | ha469
  · exact rv_piece n (469/10) (472/10) (by norm_num) (by norm_num) ha466.le hb469 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (475/10) with hb472 | ha472
  · exact rv_piece n (472/10) (475/10) (by norm_num) (by norm_num) ha469.le hb472 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (478/10) with hb475 | ha475
  · exact rv_piece n (475/10) (478/10) (by norm_num) (by norm_num) ha472.le hb475 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (481/10) with hb478 | ha478
  · exact rv_piece n (478/10) (481/10) (by norm_num) (by norm_num) ha475.le hb478 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (484/10) with hb481 | ha481
  · exact rv_piece n (481/10) (484/10) (by norm_num) (by norm_num) ha478.le hb481 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (487/10) with hb484 | ha484
  · exact rv_piece n (484/10) (487/10) (by norm_num) (by norm_num) ha481.le hb484 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (490/10) with hb487 | ha487
  · exact rv_piece n (487/10) (490/10) (by norm_num) (by norm_num) ha484.le hb487 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (493/10) with hb490 | ha490
  · exact rv_piece n (490/10) (493/10) (by norm_num) (by norm_num) ha487.le hb490 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (496/10) with hb493 | ha493
  · exact rv_piece n (493/10) (496/10) (by norm_num) (by norm_num) ha490.le hb493 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (499/10) with hb496 | ha496
  · exact rv_piece n (496/10) (499/10) (by norm_num) (by norm_num) ha493.le hb496 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (502/10) with hb499 | ha499
  · exact rv_piece n (499/10) (502/10) (by norm_num) (by norm_num) ha496.le hb499 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (505/10) with hb502 | ha502
  · exact rv_piece n (502/10) (505/10) (by norm_num) (by norm_num) ha499.le hb502 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (508/10) with hb505 | ha505
  · exact rv_piece n (505/10) (508/10) (by norm_num) (by norm_num) ha502.le hb505 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (511/10) with hb508 | ha508
  · exact rv_piece n (508/10) (511/10) (by norm_num) (by norm_num) ha505.le hb508 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (514/10) with hb511 | ha511
  · exact rv_piece n (511/10) (514/10) (by norm_num) (by norm_num) ha508.le hb511 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (517/10) with hb514 | ha514
  · exact rv_piece n (514/10) (517/10) (by norm_num) (by norm_num) ha511.le hb514 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (520/10) with hb517 | ha517
  · exact rv_piece n (517/10) (520/10) (by norm_num) (by norm_num) ha514.le hb517 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (523/10) with hb520 | ha520
  · exact rv_piece n (520/10) (523/10) (by norm_num) (by norm_num) ha517.le hb520 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (526/10) with hb523 | ha523
  · exact rv_piece n (523/10) (526/10) (by norm_num) (by norm_num) ha520.le hb523 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (529/10) with hb526 | ha526
  · exact rv_piece n (526/10) (529/10) (by norm_num) (by norm_num) ha523.le hb526 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (532/10) with hb529 | ha529
  · exact rv_piece n (529/10) (532/10) (by norm_num) (by norm_num) ha526.le hb529 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (535/10) with hb532 | ha532
  · exact rv_piece n (532/10) (535/10) (by norm_num) (by norm_num) ha529.le hb532 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (538/10) with hb535 | ha535
  · exact rv_piece n (535/10) (538/10) (by norm_num) (by norm_num) ha532.le hb535 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (541/10) with hb538 | ha538
  · exact rv_piece n (538/10) (541/10) (by norm_num) (by norm_num) ha535.le hb538 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (544/10) with hb541 | ha541
  · exact rv_piece n (541/10) (544/10) (by norm_num) (by norm_num) ha538.le hb541 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (547/10) with hb544 | ha544
  · exact rv_piece n (544/10) (547/10) (by norm_num) (by norm_num) ha541.le hb544 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (550/10) with hb547 | ha547
  · exact rv_piece n (547/10) (550/10) (by norm_num) (by norm_num) ha544.le hb547 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (553/10) with hb550 | ha550
  · exact rv_piece n (550/10) (553/10) (by norm_num) (by norm_num) ha547.le hb550 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (556/10) with hb553 | ha553
  · exact rv_piece n (553/10) (556/10) (by norm_num) (by norm_num) ha550.le hb553 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (559/10) with hb556 | ha556
  · exact rv_piece n (556/10) (559/10) (by norm_num) (by norm_num) ha553.le hb556 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (562/10) with hb559 | ha559
  · exact rv_piece n (559/10) (562/10) (by norm_num) (by norm_num) ha556.le hb559 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (565/10) with hb562 | ha562
  · exact rv_piece n (562/10) (565/10) (by norm_num) (by norm_num) ha559.le hb562 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (568/10) with hb565 | ha565
  · exact rv_piece n (565/10) (568/10) (by norm_num) (by norm_num) ha562.le hb565 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (571/10) with hb568 | ha568
  · exact rv_piece n (568/10) (571/10) (by norm_num) (by norm_num) ha565.le hb568 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (574/10) with hb571 | ha571
  · exact rv_piece n (571/10) (574/10) (by norm_num) (by norm_num) ha568.le hb571 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (577/10) with hb574 | ha574
  · exact rv_piece n (574/10) (577/10) (by norm_num) (by norm_num) ha571.le hb574 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (580/10) with hb577 | ha577
  · exact rv_piece n (577/10) (580/10) (by norm_num) (by norm_num) ha574.le hb577 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (583/10) with hb580 | ha580
  · exact rv_piece n (580/10) (583/10) (by norm_num) (by norm_num) ha577.le hb580 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (586/10) with hb583 | ha583
  · exact rv_piece n (583/10) (586/10) (by norm_num) (by norm_num) ha580.le hb583 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (589/10) with hb586 | ha586
  · exact rv_piece n (586/10) (589/10) (by norm_num) (by norm_num) ha583.le hb586 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (592/10) with hb589 | ha589
  · exact rv_piece n (589/10) (592/10) (by norm_num) (by norm_num) ha586.le hb589 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (596/10) with hb592 | ha592
  · exact rv_piece n (592/10) (596/10) (by norm_num) (by norm_num) ha589.le hb592 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (600/10) with hb596 | ha596
  · exact rv_piece n (596/10) (600/10) (by norm_num) (by norm_num) ha592.le hb596 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (604/10) with hb600 | ha600
  · exact rv_piece n (600/10) (604/10) (by norm_num) (by norm_num) ha596.le hb600 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (608/10) with hb604 | ha604
  · exact rv_piece n (604/10) (608/10) (by norm_num) (by norm_num) ha600.le hb604 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (612/10) with hb608 | ha608
  · exact rv_piece n (608/10) (612/10) (by norm_num) (by norm_num) ha604.le hb608 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (616/10) with hb612 | ha612
  · exact rv_piece n (612/10) (616/10) (by norm_num) (by norm_num) ha608.le hb612 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (620/10) with hb616 | ha616
  · exact rv_piece n (616/10) (620/10) (by norm_num) (by norm_num) ha612.le hb616 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (624/10) with hb620 | ha620
  · exact rv_piece n (620/10) (624/10) (by norm_num) (by norm_num) ha616.le hb620 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (628/10) with hb624 | ha624
  · exact rv_piece n (624/10) (628/10) (by norm_num) (by norm_num) ha620.le hb624 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (632/10) with hb628 | ha628
  · exact rv_piece n (628/10) (632/10) (by norm_num) (by norm_num) ha624.le hb628 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (636/10) with hb632 | ha632
  · exact rv_piece n (632/10) (636/10) (by norm_num) (by norm_num) ha628.le hb632 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (640/10) with hb636 | ha636
  · exact rv_piece n (636/10) (640/10) (by norm_num) (by norm_num) ha632.le hb636 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (644/10) with hb640 | ha640
  · exact rv_piece n (640/10) (644/10) (by norm_num) (by norm_num) ha636.le hb640 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (648/10) with hb644 | ha644
  · exact rv_piece n (644/10) (648/10) (by norm_num) (by norm_num) ha640.le hb644 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (652/10) with hb648 | ha648
  · exact rv_piece n (648/10) (652/10) (by norm_num) (by norm_num) ha644.le hb648 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (656/10) with hb652 | ha652
  · exact rv_piece n (652/10) (656/10) (by norm_num) (by norm_num) ha648.le hb652 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (660/10) with hb656 | ha656
  · exact rv_piece n (656/10) (660/10) (by norm_num) (by norm_num) ha652.le hb656 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (664/10) with hb660 | ha660
  · exact rv_piece n (660/10) (664/10) (by norm_num) (by norm_num) ha656.le hb660 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (668/10) with hb664 | ha664
  · exact rv_piece n (664/10) (668/10) (by norm_num) (by norm_num) ha660.le hb664 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (672/10) with hb668 | ha668
  · exact rv_piece n (668/10) (672/10) (by norm_num) (by norm_num) ha664.le hb668 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (676/10) with hb672 | ha672
  · exact rv_piece n (672/10) (676/10) (by norm_num) (by norm_num) ha668.le hb672 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (680/10) with hb676 | ha676
  · exact rv_piece n (676/10) (680/10) (by norm_num) (by norm_num) ha672.le hb676 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (684/10) with hb680 | ha680
  · exact rv_piece n (680/10) (684/10) (by norm_num) (by norm_num) ha676.le hb680 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (688/10) with hb684 | ha684
  · exact rv_piece n (684/10) (688/10) (by norm_num) (by norm_num) ha680.le hb684 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (692/10) with hb688 | ha688
  · exact rv_piece n (688/10) (692/10) (by norm_num) (by norm_num) ha684.le hb688 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (696/10) with hb692 | ha692
  · exact rv_piece n (692/10) (696/10) (by norm_num) (by norm_num) ha688.le hb692 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (700/10) with hb696 | ha696
  · exact rv_piece n (696/10) (700/10) (by norm_num) (by norm_num) ha692.le hb696 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (704/10) with hb700 | ha700
  · exact rv_piece n (700/10) (704/10) (by norm_num) (by norm_num) ha696.le hb700 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (708/10) with hb704 | ha704
  · exact rv_piece n (704/10) (708/10) (by norm_num) (by norm_num) ha700.le hb704 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (712/10) with hb708 | ha708
  · exact rv_piece n (708/10) (712/10) (by norm_num) (by norm_num) ha704.le hb708 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (716/10) with hb712 | ha712
  · exact rv_piece n (712/10) (716/10) (by norm_num) (by norm_num) ha708.le hb712 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (720/10) with hb716 | ha716
  · exact rv_piece n (716/10) (720/10) (by norm_num) (by norm_num) ha712.le hb716 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (724/10) with hb720 | ha720
  · exact rv_piece n (720/10) (724/10) (by norm_num) (by norm_num) ha716.le hb720 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (728/10) with hb724 | ha724
  · exact rv_piece n (724/10) (728/10) (by norm_num) (by norm_num) ha720.le hb724 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (732/10) with hb728 | ha728
  · exact rv_piece n (728/10) (732/10) (by norm_num) (by norm_num) ha724.le hb728 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (736/10) with hb732 | ha732
  · exact rv_piece n (732/10) (736/10) (by norm_num) (by norm_num) ha728.le hb732 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (740/10) with hb736 | ha736
  · exact rv_piece n (736/10) (740/10) (by norm_num) (by norm_num) ha732.le hb736 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (744/10) with hb740 | ha740
  · exact rv_piece n (740/10) (744/10) (by norm_num) (by norm_num) ha736.le hb740 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (748/10) with hb744 | ha744
  · exact rv_piece n (744/10) (748/10) (by norm_num) (by norm_num) ha740.le hb744 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (752/10) with hb748 | ha748
  · exact rv_piece n (748/10) (752/10) (by norm_num) (by norm_num) ha744.le hb748 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (756/10) with hb752 | ha752
  · exact rv_piece n (752/10) (756/10) (by norm_num) (by norm_num) ha748.le hb752 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (760/10) with hb756 | ha756
  · exact rv_piece n (756/10) (760/10) (by norm_num) (by norm_num) ha752.le hb756 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (764/10) with hb760 | ha760
  · exact rv_piece n (760/10) (764/10) (by norm_num) (by norm_num) ha756.le hb760 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (768/10) with hb764 | ha764
  · exact rv_piece n (764/10) (768/10) (by norm_num) (by norm_num) ha760.le hb764 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (772/10) with hb768 | ha768
  · exact rv_piece n (768/10) (772/10) (by norm_num) (by norm_num) ha764.le hb768 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (776/10) with hb772 | ha772
  · exact rv_piece n (772/10) (776/10) (by norm_num) (by norm_num) ha768.le hb772 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (780/10) with hb776 | ha776
  · exact rv_piece n (776/10) (780/10) (by norm_num) (by norm_num) ha772.le hb776 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (784/10) with hb780 | ha780
  · exact rv_piece n (780/10) (784/10) (by norm_num) (by norm_num) ha776.le hb780 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (788/10) with hb784 | ha784
  · exact rv_piece n (784/10) (788/10) (by norm_num) (by norm_num) ha780.le hb784 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (792/10) with hb788 | ha788
  · exact rv_piece n (788/10) (792/10) (by norm_num) (by norm_num) ha784.le hb788 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (796/10) with hb792 | ha792
  · exact rv_piece n (792/10) (796/10) (by norm_num) (by norm_num) ha788.le hb792 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (800/10) with hb796 | ha796
  · exact rv_piece n (796/10) (800/10) (by norm_num) (by norm_num) ha792.le hb796 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (804/10) with hb800 | ha800
  · exact rv_piece n (800/10) (804/10) (by norm_num) (by norm_num) ha796.le hb800 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (809/10) with hb804 | ha804
  · exact rv_piece n (804/10) (809/10) (by norm_num) (by norm_num) ha800.le hb804 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (814/10) with hb809 | ha809
  · exact rv_piece n (809/10) (814/10) (by norm_num) (by norm_num) ha804.le hb809 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (819/10) with hb814 | ha814
  · exact rv_piece n (814/10) (819/10) (by norm_num) (by norm_num) ha809.le hb814 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (824/10) with hb819 | ha819
  · exact rv_piece n (819/10) (824/10) (by norm_num) (by norm_num) ha814.le hb819 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (829/10) with hb824 | ha824
  · exact rv_piece n (824/10) (829/10) (by norm_num) (by norm_num) ha819.le hb824 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (834/10) with hb829 | ha829
  · exact rv_piece n (829/10) (834/10) (by norm_num) (by norm_num) ha824.le hb829 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (839/10) with hb834 | ha834
  · exact rv_piece n (834/10) (839/10) (by norm_num) (by norm_num) ha829.le hb834 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (844/10) with hb839 | ha839
  · exact rv_piece n (839/10) (844/10) (by norm_num) (by norm_num) ha834.le hb839 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (849/10) with hb844 | ha844
  · exact rv_piece n (844/10) (849/10) (by norm_num) (by norm_num) ha839.le hb844 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (854/10) with hb849 | ha849
  · exact rv_piece n (849/10) (854/10) (by norm_num) (by norm_num) ha844.le hb849 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (859/10) with hb854 | ha854
  · exact rv_piece n (854/10) (859/10) (by norm_num) (by norm_num) ha849.le hb854 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (864/10) with hb859 | ha859
  · exact rv_piece n (859/10) (864/10) (by norm_num) (by norm_num) ha854.le hb859 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (869/10) with hb864 | ha864
  · exact rv_piece n (864/10) (869/10) (by norm_num) (by norm_num) ha859.le hb864 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (874/10) with hb869 | ha869
  · exact rv_piece n (869/10) (874/10) (by norm_num) (by norm_num) ha864.le hb869 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (879/10) with hb874 | ha874
  · exact rv_piece n (874/10) (879/10) (by norm_num) (by norm_num) ha869.le hb874 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (884/10) with hb879 | ha879
  · exact rv_piece n (879/10) (884/10) (by norm_num) (by norm_num) ha874.le hb879 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (889/10) with hb884 | ha884
  · exact rv_piece n (884/10) (889/10) (by norm_num) (by norm_num) ha879.le hb884 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (894/10) with hb889 | ha889
  · exact rv_piece n (889/10) (894/10) (by norm_num) (by norm_num) ha884.le hb889 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (899/10) with hb894 | ha894
  · exact rv_piece n (894/10) (899/10) (by norm_num) (by norm_num) ha889.le hb894 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (904/10) with hb899 | ha899
  · exact rv_piece n (899/10) (904/10) (by norm_num) (by norm_num) ha894.le hb899 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (909/10) with hb904 | ha904
  · exact rv_piece n (904/10) (909/10) (by norm_num) (by norm_num) ha899.le hb904 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (914/10) with hb909 | ha909
  · exact rv_piece n (909/10) (914/10) (by norm_num) (by norm_num) ha904.le hb909 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (919/10) with hb914 | ha914
  · exact rv_piece n (914/10) (919/10) (by norm_num) (by norm_num) ha909.le hb914 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (924/10) with hb919 | ha919
  · exact rv_piece n (919/10) (924/10) (by norm_num) (by norm_num) ha914.le hb919 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (929/10) with hb924 | ha924
  · exact rv_piece n (924/10) (929/10) (by norm_num) (by norm_num) ha919.le hb924 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (934/10) with hb929 | ha929
  · exact rv_piece n (929/10) (934/10) (by norm_num) (by norm_num) ha924.le hb929 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (939/10) with hb934 | ha934
  · exact rv_piece n (934/10) (939/10) (by norm_num) (by norm_num) ha929.le hb934 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (944/10) with hb939 | ha939
  · exact rv_piece n (939/10) (944/10) (by norm_num) (by norm_num) ha934.le hb939 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (949/10) with hb944 | ha944
  · exact rv_piece n (944/10) (949/10) (by norm_num) (by norm_num) ha939.le hb944 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (954/10) with hb949 | ha949
  · exact rv_piece n (949/10) (954/10) (by norm_num) (by norm_num) ha944.le hb949 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (959/10) with hb954 | ha954
  · exact rv_piece n (954/10) (959/10) (by norm_num) (by norm_num) ha949.le hb954 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (964/10) with hb959 | ha959
  · exact rv_piece n (959/10) (964/10) (by norm_num) (by norm_num) ha954.le hb959 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (969/10) with hb964 | ha964
  · exact rv_piece n (964/10) (969/10) (by norm_num) (by norm_num) ha959.le hb964 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (974/10) with hb969 | ha969
  · exact rv_piece n (969/10) (974/10) (by norm_num) (by norm_num) ha964.le hb969 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (979/10) with hb974 | ha974
  · exact rv_piece n (974/10) (979/10) (by norm_num) (by norm_num) ha969.le hb974 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (984/10) with hb979 | ha979
  · exact rv_piece n (979/10) (984/10) (by norm_num) (by norm_num) ha974.le hb979 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (989/10) with hb984 | ha984
  · exact rv_piece n (984/10) (989/10) (by norm_num) (by norm_num) ha979.le hb984 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (994/10) with hb989 | ha989
  · exact rv_piece n (989/10) (994/10) (by norm_num) (by norm_num) ha984.le hb989 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (999/10) with hb994 | ha994
  · exact rv_piece n (994/10) (999/10) (by norm_num) (by norm_num) ha989.le hb994 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1004/10) with hb999 | ha999
  · exact rv_piece n (999/10) (1004/10) (by norm_num) (by norm_num) ha994.le hb999 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1009/10) with hb1004 | ha1004
  · exact rv_piece n (1004/10) (1009/10) (by norm_num) (by norm_num) ha999.le hb1004 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1014/10) with hb1009 | ha1009
  · exact rv_piece n (1009/10) (1014/10) (by norm_num) (by norm_num) ha1004.le hb1009 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1019/10) with hb1014 | ha1014
  · exact rv_piece n (1014/10) (1019/10) (by norm_num) (by norm_num) ha1009.le hb1014 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1024/10) with hb1019 | ha1019
  · exact rv_piece n (1019/10) (1024/10) (by norm_num) (by norm_num) ha1014.le hb1019 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1029/10) with hb1024 | ha1024
  · exact rv_piece n (1024/10) (1029/10) (by norm_num) (by norm_num) ha1019.le hb1024 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1034/10) with hb1029 | ha1029
  · exact rv_piece n (1029/10) (1034/10) (by norm_num) (by norm_num) ha1024.le hb1029 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1039/10) with hb1034 | ha1034
  · exact rv_piece n (1034/10) (1039/10) (by norm_num) (by norm_num) ha1029.le hb1034 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1044/10) with hb1039 | ha1039
  · exact rv_piece n (1039/10) (1044/10) (by norm_num) (by norm_num) ha1034.le hb1039 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1049/10) with hb1044 | ha1044
  · exact rv_piece n (1044/10) (1049/10) (by norm_num) (by norm_num) ha1039.le hb1044 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1054/10) with hb1049 | ha1049
  · exact rv_piece n (1049/10) (1054/10) (by norm_num) (by norm_num) ha1044.le hb1049 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1059/10) with hb1054 | ha1054
  · exact rv_piece n (1054/10) (1059/10) (by norm_num) (by norm_num) ha1049.le hb1054 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1064/10) with hb1059 | ha1059
  · exact rv_piece n (1059/10) (1064/10) (by norm_num) (by norm_num) ha1054.le hb1059 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1069/10) with hb1064 | ha1064
  · exact rv_piece n (1064/10) (1069/10) (by norm_num) (by norm_num) ha1059.le hb1064 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1074/10) with hb1069 | ha1069
  · exact rv_piece n (1069/10) (1074/10) (by norm_num) (by norm_num) ha1064.le hb1069 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1079/10) with hb1074 | ha1074
  · exact rv_piece n (1074/10) (1079/10) (by norm_num) (by norm_num) ha1069.le hb1074 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1084/10) with hb1079 | ha1079
  · exact rv_piece n (1079/10) (1084/10) (by norm_num) (by norm_num) ha1074.le hb1079 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1089/10) with hb1084 | ha1084
  · exact rv_piece n (1084/10) (1089/10) (by norm_num) (by norm_num) ha1079.le hb1084 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1095/10) with hb1089 | ha1089
  · exact rv_piece n (1089/10) (1095/10) (by norm_num) (by norm_num) ha1084.le hb1089 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1101/10) with hb1095 | ha1095
  · exact rv_piece n (1095/10) (1101/10) (by norm_num) (by norm_num) ha1089.le hb1095 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1107/10) with hb1101 | ha1101
  · exact rv_piece n (1101/10) (1107/10) (by norm_num) (by norm_num) ha1095.le hb1101 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1113/10) with hb1107 | ha1107
  · exact rv_piece n (1107/10) (1113/10) (by norm_num) (by norm_num) ha1101.le hb1107 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1119/10) with hb1113 | ha1113
  · exact rv_piece n (1113/10) (1119/10) (by norm_num) (by norm_num) ha1107.le hb1113 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1125/10) with hb1119 | ha1119
  · exact rv_piece n (1119/10) (1125/10) (by norm_num) (by norm_num) ha1113.le hb1119 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1131/10) with hb1125 | ha1125
  · exact rv_piece n (1125/10) (1131/10) (by norm_num) (by norm_num) ha1119.le hb1125 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1137/10) with hb1131 | ha1131
  · exact rv_piece n (1131/10) (1137/10) (by norm_num) (by norm_num) ha1125.le hb1131 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1143/10) with hb1137 | ha1137
  · exact rv_piece n (1137/10) (1143/10) (by norm_num) (by norm_num) ha1131.le hb1137 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1149/10) with hb1143 | ha1143
  · exact rv_piece n (1143/10) (1149/10) (by norm_num) (by norm_num) ha1137.le hb1143 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1155/10) with hb1149 | ha1149
  · exact rv_piece n (1149/10) (1155/10) (by norm_num) (by norm_num) ha1143.le hb1149 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1161/10) with hb1155 | ha1155
  · exact rv_piece n (1155/10) (1161/10) (by norm_num) (by norm_num) ha1149.le hb1155 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1167/10) with hb1161 | ha1161
  · exact rv_piece n (1161/10) (1167/10) (by norm_num) (by norm_num) ha1155.le hb1161 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1173/10) with hb1167 | ha1167
  · exact rv_piece n (1167/10) (1173/10) (by norm_num) (by norm_num) ha1161.le hb1167 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1179/10) with hb1173 | ha1173
  · exact rv_piece n (1173/10) (1179/10) (by norm_num) (by norm_num) ha1167.le hb1173 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1185/10) with hb1179 | ha1179
  · exact rv_piece n (1179/10) (1185/10) (by norm_num) (by norm_num) ha1173.le hb1179 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1191/10) with hb1185 | ha1185
  · exact rv_piece n (1185/10) (1191/10) (by norm_num) (by norm_num) ha1179.le hb1185 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1197/10) with hb1191 | ha1191
  · exact rv_piece n (1191/10) (1197/10) (by norm_num) (by norm_num) ha1185.le hb1191 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1203/10) with hb1197 | ha1197
  · exact rv_piece n (1197/10) (1203/10) (by norm_num) (by norm_num) ha1191.le hb1197 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1209/10) with hb1203 | ha1203
  · exact rv_piece n (1203/10) (1209/10) (by norm_num) (by norm_num) ha1197.le hb1203 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1215/10) with hb1209 | ha1209
  · exact rv_piece n (1209/10) (1215/10) (by norm_num) (by norm_num) ha1203.le hb1209 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1221/10) with hb1215 | ha1215
  · exact rv_piece n (1215/10) (1221/10) (by norm_num) (by norm_num) ha1209.le hb1215 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1227/10) with hb1221 | ha1221
  · exact rv_piece n (1221/10) (1227/10) (by norm_num) (by norm_num) ha1215.le hb1221 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1233/10) with hb1227 | ha1227
  · exact rv_piece n (1227/10) (1233/10) (by norm_num) (by norm_num) ha1221.le hb1227 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1239/10) with hb1233 | ha1233
  · exact rv_piece n (1233/10) (1239/10) (by norm_num) (by norm_num) ha1227.le hb1233 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1245/10) with hb1239 | ha1239
  · exact rv_piece n (1239/10) (1245/10) (by norm_num) (by norm_num) ha1233.le hb1239 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1251/10) with hb1245 | ha1245
  · exact rv_piece n (1245/10) (1251/10) (by norm_num) (by norm_num) ha1239.le hb1245 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1257/10) with hb1251 | ha1251
  · exact rv_piece n (1251/10) (1257/10) (by norm_num) (by norm_num) ha1245.le hb1251 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1263/10) with hb1257 | ha1257
  · exact rv_piece n (1257/10) (1263/10) (by norm_num) (by norm_num) ha1251.le hb1257 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1269/10) with hb1263 | ha1263
  · exact rv_piece n (1263/10) (1269/10) (by norm_num) (by norm_num) ha1257.le hb1263 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1275/10) with hb1269 | ha1269
  · exact rv_piece n (1269/10) (1275/10) (by norm_num) (by norm_num) ha1263.le hb1269 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1281/10) with hb1275 | ha1275
  · exact rv_piece n (1275/10) (1281/10) (by norm_num) (by norm_num) ha1269.le hb1275 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1287/10) with hb1281 | ha1281
  · exact rv_piece n (1281/10) (1287/10) (by norm_num) (by norm_num) ha1275.le hb1281 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1293/10) with hb1287 | ha1287
  · exact rv_piece n (1287/10) (1293/10) (by norm_num) (by norm_num) ha1281.le hb1287 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1299/10) with hb1293 | ha1293
  · exact rv_piece n (1293/10) (1299/10) (by norm_num) (by norm_num) ha1287.le hb1293 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1305/10) with hb1299 | ha1299
  · exact rv_piece n (1299/10) (1305/10) (by norm_num) (by norm_num) ha1293.le hb1299 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1311/10) with hb1305 | ha1305
  · exact rv_piece n (1305/10) (1311/10) (by norm_num) (by norm_num) ha1299.le hb1305 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1317/10) with hb1311 | ha1311
  · exact rv_piece n (1311/10) (1317/10) (by norm_num) (by norm_num) ha1305.le hb1311 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1323/10) with hb1317 | ha1317
  · exact rv_piece n (1317/10) (1323/10) (by norm_num) (by norm_num) ha1311.le hb1317 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1329/10) with hb1323 | ha1323
  · exact rv_piece n (1323/10) (1329/10) (by norm_num) (by norm_num) ha1317.le hb1323 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1335/10) with hb1329 | ha1329
  · exact rv_piece n (1329/10) (1335/10) (by norm_num) (by norm_num) ha1323.le hb1329 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1341/10) with hb1335 | ha1335
  · exact rv_piece n (1335/10) (1341/10) (by norm_num) (by norm_num) ha1329.le hb1335 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1347/10) with hb1341 | ha1341
  · exact rv_piece n (1341/10) (1347/10) (by norm_num) (by norm_num) ha1335.le hb1341 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1353/10) with hb1347 | ha1347
  · exact rv_piece n (1347/10) (1353/10) (by norm_num) (by norm_num) ha1341.le hb1347 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1359/10) with hb1353 | ha1353
  · exact rv_piece n (1353/10) (1359/10) (by norm_num) (by norm_num) ha1347.le hb1353 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1365/10) with hb1359 | ha1359
  · exact rv_piece n (1359/10) (1365/10) (by norm_num) (by norm_num) ha1353.le hb1359 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1371/10) with hb1365 | ha1365
  · exact rv_piece n (1365/10) (1371/10) (by norm_num) (by norm_num) ha1359.le hb1365 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1377/10) with hb1371 | ha1371
  · exact rv_piece n (1371/10) (1377/10) (by norm_num) (by norm_num) ha1365.le hb1371 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1383/10) with hb1377 | ha1377
  · exact rv_piece n (1377/10) (1383/10) (by norm_num) (by norm_num) ha1371.le hb1377 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1389/10) with hb1383 | ha1383
  · exact rv_piece n (1383/10) (1389/10) (by norm_num) (by norm_num) ha1377.le hb1383 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1395/10) with hb1389 | ha1389
  · exact rv_piece n (1389/10) (1395/10) (by norm_num) (by norm_num) ha1383.le hb1389 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1401/10) with hb1395 | ha1395
  · exact rv_piece n (1395/10) (1401/10) (by norm_num) (by norm_num) ha1389.le hb1395 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1407/10) with hb1401 | ha1401
  · exact rv_piece n (1401/10) (1407/10) (by norm_num) (by norm_num) ha1395.le hb1401 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1413/10) with hb1407 | ha1407
  · exact rv_piece n (1407/10) (1413/10) (by norm_num) (by norm_num) ha1401.le hb1407 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1419/10) with hb1413 | ha1413
  · exact rv_piece n (1413/10) (1419/10) (by norm_num) (by norm_num) ha1407.le hb1413 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1425/10) with hb1419 | ha1419
  · exact rv_piece n (1419/10) (1425/10) (by norm_num) (by norm_num) ha1413.le hb1419 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1431/10) with hb1425 | ha1425
  · exact rv_piece n (1425/10) (1431/10) (by norm_num) (by norm_num) ha1419.le hb1425 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1437/10) with hb1431 | ha1431
  · exact rv_piece n (1431/10) (1437/10) (by norm_num) (by norm_num) ha1425.le hb1431 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1443/10) with hb1437 | ha1437
  · exact rv_piece n (1437/10) (1443/10) (by norm_num) (by norm_num) ha1431.le hb1437 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1449/10) with hb1443 | ha1443
  · exact rv_piece n (1443/10) (1449/10) (by norm_num) (by norm_num) ha1437.le hb1443 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1455/10) with hb1449 | ha1449
  · exact rv_piece n (1449/10) (1455/10) (by norm_num) (by norm_num) ha1443.le hb1449 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1461/10) with hb1455 | ha1455
  · exact rv_piece n (1455/10) (1461/10) (by norm_num) (by norm_num) ha1449.le hb1455 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1467/10) with hb1461 | ha1461
  · exact rv_piece n (1461/10) (1467/10) (by norm_num) (by norm_num) ha1455.le hb1461 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1473/10) with hb1467 | ha1467
  · exact rv_piece n (1467/10) (1473/10) (by norm_num) (by norm_num) ha1461.le hb1467 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1479/10) with hb1473 | ha1473
  · exact rv_piece n (1473/10) (1479/10) (by norm_num) (by norm_num) ha1467.le hb1473 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1485/10) with hb1479 | ha1479
  · exact rv_piece n (1479/10) (1485/10) (by norm_num) (by norm_num) ha1473.le hb1479 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1491/10) with hb1485 | ha1485
  · exact rv_piece n (1485/10) (1491/10) (by norm_num) (by norm_num) ha1479.le hb1485 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1497/10) with hb1491 | ha1491
  · exact rv_piece n (1491/10) (1497/10) (by norm_num) (by norm_num) ha1485.le hb1491 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1503/10) with hb1497 | ha1497
  · exact rv_piece n (1497/10) (1503/10) (by norm_num) (by norm_num) ha1491.le hb1497 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1509/10) with hb1503 | ha1503
  · exact rv_piece n (1503/10) (1509/10) (by norm_num) (by norm_num) ha1497.le hb1503 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1515/10) with hb1509 | ha1509
  · exact rv_piece n (1509/10) (1515/10) (by norm_num) (by norm_num) ha1503.le hb1509 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1521/10) with hb1515 | ha1515
  · exact rv_piece n (1515/10) (1521/10) (by norm_num) (by norm_num) ha1509.le hb1515 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1527/10) with hb1521 | ha1521
  · exact rv_piece n (1521/10) (1527/10) (by norm_num) (by norm_num) ha1515.le hb1521 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1533/10) with hb1527 | ha1527
  · exact rv_piece n (1527/10) (1533/10) (by norm_num) (by norm_num) ha1521.le hb1527 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1539/10) with hb1533 | ha1533
  · exact rv_piece n (1533/10) (1539/10) (by norm_num) (by norm_num) ha1527.le hb1533 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1545/10) with hb1539 | ha1539
  · exact rv_piece n (1539/10) (1545/10) (by norm_num) (by norm_num) ha1533.le hb1539 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1551/10) with hb1545 | ha1545
  · exact rv_piece n (1545/10) (1551/10) (by norm_num) (by norm_num) ha1539.le hb1545 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1557/10) with hb1551 | ha1551
  · exact rv_piece n (1551/10) (1557/10) (by norm_num) (by norm_num) ha1545.le hb1551 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1563/10) with hb1557 | ha1557
  · exact rv_piece n (1557/10) (1563/10) (by norm_num) (by norm_num) ha1551.le hb1557 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1569/10) with hb1563 | ha1563
  · exact rv_piece n (1563/10) (1569/10) (by norm_num) (by norm_num) ha1557.le hb1563 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1575/10) with hb1569 | ha1569
  · exact rv_piece n (1569/10) (1575/10) (by norm_num) (by norm_num) ha1563.le hb1569 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1581/10) with hb1575 | ha1575
  · exact rv_piece n (1575/10) (1581/10) (by norm_num) (by norm_num) ha1569.le hb1575 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1587/10) with hb1581 | ha1581
  · exact rv_piece n (1581/10) (1587/10) (by norm_num) (by norm_num) ha1575.le hb1581 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1593/10) with hb1587 | ha1587
  · exact rv_piece n (1587/10) (1593/10) (by norm_num) (by norm_num) ha1581.le hb1587 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1599/10) with hb1593 | ha1593
  · exact rv_piece n (1593/10) (1599/10) (by norm_num) (by norm_num) ha1587.le hb1593 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1605/10) with hb1599 | ha1599
  · exact rv_piece n (1599/10) (1605/10) (by norm_num) (by norm_num) ha1593.le hb1599 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1611/10) with hb1605 | ha1605
  · exact rv_piece n (1605/10) (1611/10) (by norm_num) (by norm_num) ha1599.le hb1605 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1617/10) with hb1611 | ha1611
  · exact rv_piece n (1611/10) (1617/10) (by norm_num) (by norm_num) ha1605.le hb1611 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1623/10) with hb1617 | ha1617
  · exact rv_piece n (1617/10) (1623/10) (by norm_num) (by norm_num) ha1611.le hb1617 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1629/10) with hb1623 | ha1623
  · exact rv_piece n (1623/10) (1629/10) (by norm_num) (by norm_num) ha1617.le hb1623 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1635/10) with hb1629 | ha1629
  · exact rv_piece n (1629/10) (1635/10) (by norm_num) (by norm_num) ha1623.le hb1629 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1641/10) with hb1635 | ha1635
  · exact rv_piece n (1635/10) (1641/10) (by norm_num) (by norm_num) ha1629.le hb1635 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1647/10) with hb1641 | ha1641
  · exact rv_piece n (1641/10) (1647/10) (by norm_num) (by norm_num) ha1635.le hb1641 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1653/10) with hb1647 | ha1647
  · exact rv_piece n (1647/10) (1653/10) (by norm_num) (by norm_num) ha1641.le hb1647 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1659/10) with hb1653 | ha1653
  · exact rv_piece n (1653/10) (1659/10) (by norm_num) (by norm_num) ha1647.le hb1653 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1665/10) with hb1659 | ha1659
  · exact rv_piece n (1659/10) (1665/10) (by norm_num) (by norm_num) ha1653.le hb1659 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1671/10) with hb1665 | ha1665
  · exact rv_piece n (1665/10) (1671/10) (by norm_num) (by norm_num) ha1659.le hb1665 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1677/10) with hb1671 | ha1671
  · exact rv_piece n (1671/10) (1677/10) (by norm_num) (by norm_num) ha1665.le hb1671 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1683/10) with hb1677 | ha1677
  · exact rv_piece n (1677/10) (1683/10) (by norm_num) (by norm_num) ha1671.le hb1677 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1689/10) with hb1683 | ha1683
  · exact rv_piece n (1683/10) (1689/10) (by norm_num) (by norm_num) ha1677.le hb1683 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1695/10) with hb1689 | ha1689
  · exact rv_piece n (1689/10) (1695/10) (by norm_num) (by norm_num) ha1683.le hb1689 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1701/10) with hb1695 | ha1695
  · exact rv_piece n (1695/10) (1701/10) (by norm_num) (by norm_num) ha1689.le hb1695 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1707/10) with hb1701 | ha1701
  · exact rv_piece n (1701/10) (1707/10) (by norm_num) (by norm_num) ha1695.le hb1701 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1713/10) with hb1707 | ha1707
  · exact rv_piece n (1707/10) (1713/10) (by norm_num) (by norm_num) ha1701.le hb1707 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1719/10) with hb1713 | ha1713
  · exact rv_piece n (1713/10) (1719/10) (by norm_num) (by norm_num) ha1707.le hb1713 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1725/10) with hb1719 | ha1719
  · exact rv_piece n (1719/10) (1725/10) (by norm_num) (by norm_num) ha1713.le hb1719 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1731/10) with hb1725 | ha1725
  · exact rv_piece n (1725/10) (1731/10) (by norm_num) (by norm_num) ha1719.le hb1725 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1737/10) with hb1731 | ha1731
  · exact rv_piece n (1731/10) (1737/10) (by norm_num) (by norm_num) ha1725.le hb1731 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1743/10) with hb1737 | ha1737
  · exact rv_piece n (1737/10) (1743/10) (by norm_num) (by norm_num) ha1731.le hb1737 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1749/10) with hb1743 | ha1743
  · exact rv_piece n (1743/10) (1749/10) (by norm_num) (by norm_num) ha1737.le hb1743 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1755/10) with hb1749 | ha1749
  · exact rv_piece n (1749/10) (1755/10) (by norm_num) (by norm_num) ha1743.le hb1749 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1761/10) with hb1755 | ha1755
  · exact rv_piece n (1755/10) (1761/10) (by norm_num) (by norm_num) ha1749.le hb1755 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1767/10) with hb1761 | ha1761
  · exact rv_piece n (1761/10) (1767/10) (by norm_num) (by norm_num) ha1755.le hb1761 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1773/10) with hb1767 | ha1767
  · exact rv_piece n (1767/10) (1773/10) (by norm_num) (by norm_num) ha1761.le hb1767 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1779/10) with hb1773 | ha1773
  · exact rv_piece n (1773/10) (1779/10) (by norm_num) (by norm_num) ha1767.le hb1773 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1785/10) with hb1779 | ha1779
  · exact rv_piece n (1779/10) (1785/10) (by norm_num) (by norm_num) ha1773.le hb1779 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1791/10) with hb1785 | ha1785
  · exact rv_piece n (1785/10) (1791/10) (by norm_num) (by norm_num) ha1779.le hb1785 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1797/10) with hb1791 | ha1791
  · exact rv_piece n (1791/10) (1797/10) (by norm_num) (by norm_num) ha1785.le hb1791 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1803/10) with hb1797 | ha1797
  · exact rv_piece n (1797/10) (1803/10) (by norm_num) (by norm_num) ha1791.le hb1797 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1809/10) with hb1803 | ha1803
  · exact rv_piece n (1803/10) (1809/10) (by norm_num) (by norm_num) ha1797.le hb1803 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1815/10) with hb1809 | ha1809
  · exact rv_piece n (1809/10) (1815/10) (by norm_num) (by norm_num) ha1803.le hb1809 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1821/10) with hb1815 | ha1815
  · exact rv_piece n (1815/10) (1821/10) (by norm_num) (by norm_num) ha1809.le hb1815 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1827/10) with hb1821 | ha1821
  · exact rv_piece n (1821/10) (1827/10) (by norm_num) (by norm_num) ha1815.le hb1821 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1833/10) with hb1827 | ha1827
  · exact rv_piece n (1827/10) (1833/10) (by norm_num) (by norm_num) ha1821.le hb1827 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1839/10) with hb1833 | ha1833
  · exact rv_piece n (1833/10) (1839/10) (by norm_num) (by norm_num) ha1827.le hb1833 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1845/10) with hb1839 | ha1839
  · exact rv_piece n (1839/10) (1845/10) (by norm_num) (by norm_num) ha1833.le hb1839 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1851/10) with hb1845 | ha1845
  · exact rv_piece n (1845/10) (1851/10) (by norm_num) (by norm_num) ha1839.le hb1845 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1857/10) with hb1851 | ha1851
  · exact rv_piece n (1851/10) (1857/10) (by norm_num) (by norm_num) ha1845.le hb1851 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1863/10) with hb1857 | ha1857
  · exact rv_piece n (1857/10) (1863/10) (by norm_num) (by norm_num) ha1851.le hb1857 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1869/10) with hb1863 | ha1863
  · exact rv_piece n (1863/10) (1869/10) (by norm_num) (by norm_num) ha1857.le hb1863 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1875/10) with hb1869 | ha1869
  · exact rv_piece n (1869/10) (1875/10) (by norm_num) (by norm_num) ha1863.le hb1869 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1881/10) with hb1875 | ha1875
  · exact rv_piece n (1875/10) (1881/10) (by norm_num) (by norm_num) ha1869.le hb1875 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1887/10) with hb1881 | ha1881
  · exact rv_piece n (1881/10) (1887/10) (by norm_num) (by norm_num) ha1875.le hb1881 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1893/10) with hb1887 | ha1887
  · exact rv_piece n (1887/10) (1893/10) (by norm_num) (by norm_num) ha1881.le hb1887 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1899/10) with hb1893 | ha1893
  · exact rv_piece n (1893/10) (1899/10) (by norm_num) (by norm_num) ha1887.le hb1893 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1905/10) with hb1899 | ha1899
  · exact rv_piece n (1899/10) (1905/10) (by norm_num) (by norm_num) ha1893.le hb1899 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1911/10) with hb1905 | ha1905
  · exact rv_piece n (1905/10) (1911/10) (by norm_num) (by norm_num) ha1899.le hb1905 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1917/10) with hb1911 | ha1911
  · exact rv_piece n (1911/10) (1917/10) (by norm_num) (by norm_num) ha1905.le hb1911 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1923/10) with hb1917 | ha1917
  · exact rv_piece n (1917/10) (1923/10) (by norm_num) (by norm_num) ha1911.le hb1917 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1929/10) with hb1923 | ha1923
  · exact rv_piece n (1923/10) (1929/10) (by norm_num) (by norm_num) ha1917.le hb1923 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1935/10) with hb1929 | ha1929
  · exact rv_piece n (1929/10) (1935/10) (by norm_num) (by norm_num) ha1923.le hb1929 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1941/10) with hb1935 | ha1935
  · exact rv_piece n (1935/10) (1941/10) (by norm_num) (by norm_num) ha1929.le hb1935 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1947/10) with hb1941 | ha1941
  · exact rv_piece n (1941/10) (1947/10) (by norm_num) (by norm_num) ha1935.le hb1941 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1953/10) with hb1947 | ha1947
  · exact rv_piece n (1947/10) (1953/10) (by norm_num) (by norm_num) ha1941.le hb1947 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1959/10) with hb1953 | ha1953
  · exact rv_piece n (1953/10) (1959/10) (by norm_num) (by norm_num) ha1947.le hb1953 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1965/10) with hb1959 | ha1959
  · exact rv_piece n (1959/10) (1965/10) (by norm_num) (by norm_num) ha1953.le hb1959 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1971/10) with hb1965 | ha1965
  · exact rv_piece n (1965/10) (1971/10) (by norm_num) (by norm_num) ha1959.le hb1965 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1977/10) with hb1971 | ha1971
  · exact rv_piece n (1971/10) (1977/10) (by norm_num) (by norm_num) ha1965.le hb1971 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1983/10) with hb1977 | ha1977
  · exact rv_piece n (1977/10) (1983/10) (by norm_num) (by norm_num) ha1971.le hb1977 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1989/10) with hb1983 | ha1983
  · exact rv_piece n (1983/10) (1989/10) (by norm_num) (by norm_num) ha1977.le hb1983 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (1995/10) with hb1989 | ha1989
  · exact rv_piece n (1989/10) (1995/10) (by norm_num) (by norm_num) ha1983.le hb1989 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2001/10) with hb1995 | ha1995
  · exact rv_piece n (1995/10) (2001/10) (by norm_num) (by norm_num) ha1989.le hb1995 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2007/10) with hb2001 | ha2001
  · exact rv_piece n (2001/10) (2007/10) (by norm_num) (by norm_num) ha1995.le hb2001 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2013/10) with hb2007 | ha2007
  · exact rv_piece n (2007/10) (2013/10) (by norm_num) (by norm_num) ha2001.le hb2007 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2019/10) with hb2013 | ha2013
  · exact rv_piece n (2013/10) (2019/10) (by norm_num) (by norm_num) ha2007.le hb2013 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2025/10) with hb2019 | ha2019
  · exact rv_piece n (2019/10) (2025/10) (by norm_num) (by norm_num) ha2013.le hb2019 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2031/10) with hb2025 | ha2025
  · exact rv_piece n (2025/10) (2031/10) (by norm_num) (by norm_num) ha2019.le hb2025 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2037/10) with hb2031 | ha2031
  · exact rv_piece n (2031/10) (2037/10) (by norm_num) (by norm_num) ha2025.le hb2031 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2043/10) with hb2037 | ha2037
  · exact rv_piece n (2037/10) (2043/10) (by norm_num) (by norm_num) ha2031.le hb2037 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2049/10) with hb2043 | ha2043
  · exact rv_piece n (2043/10) (2049/10) (by norm_num) (by norm_num) ha2037.le hb2043 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2055/10) with hb2049 | ha2049
  · exact rv_piece n (2049/10) (2055/10) (by norm_num) (by norm_num) ha2043.le hb2049 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2061/10) with hb2055 | ha2055
  · exact rv_piece n (2055/10) (2061/10) (by norm_num) (by norm_num) ha2049.le hb2055 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2067/10) with hb2061 | ha2061
  · exact rv_piece n (2061/10) (2067/10) (by norm_num) (by norm_num) ha2055.le hb2061 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2073/10) with hb2067 | ha2067
  · exact rv_piece n (2067/10) (2073/10) (by norm_num) (by norm_num) ha2061.le hb2067 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2079/10) with hb2073 | ha2073
  · exact rv_piece n (2073/10) (2079/10) (by norm_num) (by norm_num) ha2067.le hb2073 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2085/10) with hb2079 | ha2079
  · exact rv_piece n (2079/10) (2085/10) (by norm_num) (by norm_num) ha2073.le hb2079 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2091/10) with hb2085 | ha2085
  · exact rv_piece n (2085/10) (2091/10) (by norm_num) (by norm_num) ha2079.le hb2085 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2097/10) with hb2091 | ha2091
  · exact rv_piece n (2091/10) (2097/10) (by norm_num) (by norm_num) ha2085.le hb2091 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2103/10) with hb2097 | ha2097
  · exact rv_piece n (2097/10) (2103/10) (by norm_num) (by norm_num) ha2091.le hb2097 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2109/10) with hb2103 | ha2103
  · exact rv_piece n (2103/10) (2109/10) (by norm_num) (by norm_num) ha2097.le hb2103 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2115/10) with hb2109 | ha2109
  · exact rv_piece n (2109/10) (2115/10) (by norm_num) (by norm_num) ha2103.le hb2109 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2121/10) with hb2115 | ha2115
  · exact rv_piece n (2115/10) (2121/10) (by norm_num) (by norm_num) ha2109.le hb2115 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2127/10) with hb2121 | ha2121
  · exact rv_piece n (2121/10) (2127/10) (by norm_num) (by norm_num) ha2115.le hb2121 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2133/10) with hb2127 | ha2127
  · exact rv_piece n (2127/10) (2133/10) (by norm_num) (by norm_num) ha2121.le hb2127 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2139/10) with hb2133 | ha2133
  · exact rv_piece n (2133/10) (2139/10) (by norm_num) (by norm_num) ha2127.le hb2133 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2145/10) with hb2139 | ha2139
  · exact rv_piece n (2139/10) (2145/10) (by norm_num) (by norm_num) ha2133.le hb2139 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2151/10) with hb2145 | ha2145
  · exact rv_piece n (2145/10) (2151/10) (by norm_num) (by norm_num) ha2139.le hb2145 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2157/10) with hb2151 | ha2151
  · exact rv_piece n (2151/10) (2157/10) (by norm_num) (by norm_num) ha2145.le hb2151 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2163/10) with hb2157 | ha2157
  · exact rv_piece n (2157/10) (2163/10) (by norm_num) (by norm_num) ha2151.le hb2157 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2169/10) with hb2163 | ha2163
  · exact rv_piece n (2163/10) (2169/10) (by norm_num) (by norm_num) ha2157.le hb2163 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2175/10) with hb2169 | ha2169
  · exact rv_piece n (2169/10) (2175/10) (by norm_num) (by norm_num) ha2163.le hb2169 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2181/10) with hb2175 | ha2175
  · exact rv_piece n (2175/10) (2181/10) (by norm_num) (by norm_num) ha2169.le hb2175 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2187/10) with hb2181 | ha2181
  · exact rv_piece n (2181/10) (2187/10) (by norm_num) (by norm_num) ha2175.le hb2181 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2193/10) with hb2187 | ha2187
  · exact rv_piece n (2187/10) (2193/10) (by norm_num) (by norm_num) ha2181.le hb2187 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2199/10) with hb2193 | ha2193
  · exact rv_piece n (2193/10) (2199/10) (by norm_num) (by norm_num) ha2187.le hb2193 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2205/10) with hb2199 | ha2199
  · exact rv_piece n (2199/10) (2205/10) (by norm_num) (by norm_num) ha2193.le hb2199 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2211/10) with hb2205 | ha2205
  · exact rv_piece n (2205/10) (2211/10) (by norm_num) (by norm_num) ha2199.le hb2205 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2217/10) with hb2211 | ha2211
  · exact rv_piece n (2211/10) (2217/10) (by norm_num) (by norm_num) ha2205.le hb2211 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2222/10) with hb2217 | ha2217
  · exact rv_piece n (2217/10) (2222/10) (by norm_num) (by norm_num) ha2211.le hb2217 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2227/10) with hb2222 | ha2222
  · exact rv_piece n (2222/10) (2227/10) (by norm_num) (by norm_num) ha2217.le hb2222 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2232/10) with hb2227 | ha2227
  · exact rv_piece n (2227/10) (2232/10) (by norm_num) (by norm_num) ha2222.le hb2227 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2237/10) with hb2232 | ha2232
  · exact rv_piece n (2232/10) (2237/10) (by norm_num) (by norm_num) ha2227.le hb2232 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2242/10) with hb2237 | ha2237
  · exact rv_piece n (2237/10) (2242/10) (by norm_num) (by norm_num) ha2232.le hb2237 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2247/10) with hb2242 | ha2242
  · exact rv_piece n (2242/10) (2247/10) (by norm_num) (by norm_num) ha2237.le hb2242 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2252/10) with hb2247 | ha2247
  · exact rv_piece n (2247/10) (2252/10) (by norm_num) (by norm_num) ha2242.le hb2247 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2257/10) with hb2252 | ha2252
  · exact rv_piece n (2252/10) (2257/10) (by norm_num) (by norm_num) ha2247.le hb2252 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2262/10) with hb2257 | ha2257
  · exact rv_piece n (2257/10) (2262/10) (by norm_num) (by norm_num) ha2252.le hb2257 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2267/10) with hb2262 | ha2262
  · exact rv_piece n (2262/10) (2267/10) (by norm_num) (by norm_num) ha2257.le hb2262 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2272/10) with hb2267 | ha2267
  · exact rv_piece n (2267/10) (2272/10) (by norm_num) (by norm_num) ha2262.le hb2267 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2277/10) with hb2272 | ha2272
  · exact rv_piece n (2272/10) (2277/10) (by norm_num) (by norm_num) ha2267.le hb2272 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2282/10) with hb2277 | ha2277
  · exact rv_piece n (2277/10) (2282/10) (by norm_num) (by norm_num) ha2272.le hb2277 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2287/10) with hb2282 | ha2282
  · exact rv_piece n (2282/10) (2287/10) (by norm_num) (by norm_num) ha2277.le hb2282 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2292/10) with hb2287 | ha2287
  · exact rv_piece n (2287/10) (2292/10) (by norm_num) (by norm_num) ha2282.le hb2287 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2297/10) with hb2292 | ha2292
  · exact rv_piece n (2292/10) (2297/10) (by norm_num) (by norm_num) ha2287.le hb2292 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2302/10) with hb2297 | ha2297
  · exact rv_piece n (2297/10) (2302/10) (by norm_num) (by norm_num) ha2292.le hb2297 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2307/10) with hb2302 | ha2302
  · exact rv_piece n (2302/10) (2307/10) (by norm_num) (by norm_num) ha2297.le hb2302 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2312/10) with hb2307 | ha2307
  · exact rv_piece n (2307/10) (2312/10) (by norm_num) (by norm_num) ha2302.le hb2307 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2317/10) with hb2312 | ha2312
  · exact rv_piece n (2312/10) (2317/10) (by norm_num) (by norm_num) ha2307.le hb2312 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2322/10) with hb2317 | ha2317
  · exact rv_piece n (2317/10) (2322/10) (by norm_num) (by norm_num) ha2312.le hb2317 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2327/10) with hb2322 | ha2322
  · exact rv_piece n (2322/10) (2327/10) (by norm_num) (by norm_num) ha2317.le hb2322 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2332/10) with hb2327 | ha2327
  · exact rv_piece n (2327/10) (2332/10) (by norm_num) (by norm_num) ha2322.le hb2327 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2337/10) with hb2332 | ha2332
  · exact rv_piece n (2332/10) (2337/10) (by norm_num) (by norm_num) ha2327.le hb2332 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2342/10) with hb2337 | ha2337
  · exact rv_piece n (2337/10) (2342/10) (by norm_num) (by norm_num) ha2332.le hb2337 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2347/10) with hb2342 | ha2342
  · exact rv_piece n (2342/10) (2347/10) (by norm_num) (by norm_num) ha2337.le hb2342 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2352/10) with hb2347 | ha2347
  · exact rv_piece n (2347/10) (2352/10) (by norm_num) (by norm_num) ha2342.le hb2347 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2357/10) with hb2352 | ha2352
  · exact rv_piece n (2352/10) (2357/10) (by norm_num) (by norm_num) ha2347.le hb2352 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2362/10) with hb2357 | ha2357
  · exact rv_piece n (2357/10) (2362/10) (by norm_num) (by norm_num) ha2352.le hb2357 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2367/10) with hb2362 | ha2362
  · exact rv_piece n (2362/10) (2367/10) (by norm_num) (by norm_num) ha2357.le hb2362 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2372/10) with hb2367 | ha2367
  · exact rv_piece n (2367/10) (2372/10) (by norm_num) (by norm_num) ha2362.le hb2367 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2377/10) with hb2372 | ha2372
  · exact rv_piece n (2372/10) (2377/10) (by norm_num) (by norm_num) ha2367.le hb2372 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2382/10) with hb2377 | ha2377
  · exact rv_piece n (2377/10) (2382/10) (by norm_num) (by norm_num) ha2372.le hb2377 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2387/10) with hb2382 | ha2382
  · exact rv_piece n (2382/10) (2387/10) (by norm_num) (by norm_num) ha2377.le hb2382 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2392/10) with hb2387 | ha2387
  · exact rv_piece n (2387/10) (2392/10) (by norm_num) (by norm_num) ha2382.le hb2387 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2397/10) with hb2392 | ha2392
  · exact rv_piece n (2392/10) (2397/10) (by norm_num) (by norm_num) ha2387.le hb2392 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2402/10) with hb2397 | ha2397
  · exact rv_piece n (2397/10) (2402/10) (by norm_num) (by norm_num) ha2392.le hb2397 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2407/10) with hb2402 | ha2402
  · exact rv_piece n (2402/10) (2407/10) (by norm_num) (by norm_num) ha2397.le hb2402 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2412/10) with hb2407 | ha2407
  · exact rv_piece n (2407/10) (2412/10) (by norm_num) (by norm_num) ha2402.le hb2407 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2417/10) with hb2412 | ha2412
  · exact rv_piece n (2412/10) (2417/10) (by norm_num) (by norm_num) ha2407.le hb2412 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2422/10) with hb2417 | ha2417
  · exact rv_piece n (2417/10) (2422/10) (by norm_num) (by norm_num) ha2412.le hb2417 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2427/10) with hb2422 | ha2422
  · exact rv_piece n (2422/10) (2427/10) (by norm_num) (by norm_num) ha2417.le hb2422 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2432/10) with hb2427 | ha2427
  · exact rv_piece n (2427/10) (2432/10) (by norm_num) (by norm_num) ha2422.le hb2427 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2437/10) with hb2432 | ha2432
  · exact rv_piece n (2432/10) (2437/10) (by norm_num) (by norm_num) ha2427.le hb2432 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2442/10) with hb2437 | ha2437
  · exact rv_piece n (2437/10) (2442/10) (by norm_num) (by norm_num) ha2432.le hb2437 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2447/10) with hb2442 | ha2442
  · exact rv_piece n (2442/10) (2447/10) (by norm_num) (by norm_num) ha2437.le hb2442 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2452/10) with hb2447 | ha2447
  · exact rv_piece n (2447/10) (2452/10) (by norm_num) (by norm_num) ha2442.le hb2447 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2457/10) with hb2452 | ha2452
  · exact rv_piece n (2452/10) (2457/10) (by norm_num) (by norm_num) ha2447.le hb2452 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2462/10) with hb2457 | ha2457
  · exact rv_piece n (2457/10) (2462/10) (by norm_num) (by norm_num) ha2452.le hb2457 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2467/10) with hb2462 | ha2462
  · exact rv_piece n (2462/10) (2467/10) (by norm_num) (by norm_num) ha2457.le hb2462 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2472/10) with hb2467 | ha2467
  · exact rv_piece n (2467/10) (2472/10) (by norm_num) (by norm_num) ha2462.le hb2467 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2477/10) with hb2472 | ha2472
  · exact rv_piece n (2472/10) (2477/10) (by norm_num) (by norm_num) ha2467.le hb2472 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2482/10) with hb2477 | ha2477
  · exact rv_piece n (2477/10) (2482/10) (by norm_num) (by norm_num) ha2472.le hb2477 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2487/10) with hb2482 | ha2482
  · exact rv_piece n (2482/10) (2487/10) (by norm_num) (by norm_num) ha2477.le hb2482 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2492/10) with hb2487 | ha2487
  · exact rv_piece n (2487/10) (2492/10) (by norm_num) (by norm_num) ha2482.le hb2487 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2497/10) with hb2492 | ha2492
  · exact rv_piece n (2492/10) (2497/10) (by norm_num) (by norm_num) ha2487.le hb2492 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2502/10) with hb2497 | ha2497
  · exact rv_piece n (2497/10) (2502/10) (by norm_num) (by norm_num) ha2492.le hb2497 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2506/10) with hb2502 | ha2502
  · exact rv_piece n (2502/10) (2506/10) (by norm_num) (by norm_num) ha2497.le hb2502 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2510/10) with hb2506 | ha2506
  · exact rv_piece n (2506/10) (2510/10) (by norm_num) (by norm_num) ha2502.le hb2506 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2514/10) with hb2510 | ha2510
  · exact rv_piece n (2510/10) (2514/10) (by norm_num) (by norm_num) ha2506.le hb2510 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2518/10) with hb2514 | ha2514
  · exact rv_piece n (2514/10) (2518/10) (by norm_num) (by norm_num) ha2510.le hb2514 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2522/10) with hb2518 | ha2518
  · exact rv_piece n (2518/10) (2522/10) (by norm_num) (by norm_num) ha2514.le hb2518 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2526/10) with hb2522 | ha2522
  · exact rv_piece n (2522/10) (2526/10) (by norm_num) (by norm_num) ha2518.le hb2522 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2530/10) with hb2526 | ha2526
  · exact rv_piece n (2526/10) (2530/10) (by norm_num) (by norm_num) ha2522.le hb2526 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2534/10) with hb2530 | ha2530
  · exact rv_piece n (2530/10) (2534/10) (by norm_num) (by norm_num) ha2526.le hb2530 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2538/10) with hb2534 | ha2534
  · exact rv_piece n (2534/10) (2538/10) (by norm_num) (by norm_num) ha2530.le hb2534 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2542/10) with hb2538 | ha2538
  · exact rv_piece n (2538/10) (2542/10) (by norm_num) (by norm_num) ha2534.le hb2538 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2546/10) with hb2542 | ha2542
  · exact rv_piece n (2542/10) (2546/10) (by norm_num) (by norm_num) ha2538.le hb2542 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2550/10) with hb2546 | ha2546
  · exact rv_piece n (2546/10) (2550/10) (by norm_num) (by norm_num) ha2542.le hb2546 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2554/10) with hb2550 | ha2550
  · exact rv_piece n (2550/10) (2554/10) (by norm_num) (by norm_num) ha2546.le hb2550 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2558/10) with hb2554 | ha2554
  · exact rv_piece n (2554/10) (2558/10) (by norm_num) (by norm_num) ha2550.le hb2554 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2562/10) with hb2558 | ha2558
  · exact rv_piece n (2558/10) (2562/10) (by norm_num) (by norm_num) ha2554.le hb2558 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2566/10) with hb2562 | ha2562
  · exact rv_piece n (2562/10) (2566/10) (by norm_num) (by norm_num) ha2558.le hb2562 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2570/10) with hb2566 | ha2566
  · exact rv_piece n (2566/10) (2570/10) (by norm_num) (by norm_num) ha2562.le hb2566 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2574/10) with hb2570 | ha2570
  · exact rv_piece n (2570/10) (2574/10) (by norm_num) (by norm_num) ha2566.le hb2570 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2578/10) with hb2574 | ha2574
  · exact rv_piece n (2574/10) (2578/10) (by norm_num) (by norm_num) ha2570.le hb2574 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2582/10) with hb2578 | ha2578
  · exact rv_piece n (2578/10) (2582/10) (by norm_num) (by norm_num) ha2574.le hb2578 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2586/10) with hb2582 | ha2582
  · exact rv_piece n (2582/10) (2586/10) (by norm_num) (by norm_num) ha2578.le hb2582 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2590/10) with hb2586 | ha2586
  · exact rv_piece n (2586/10) (2590/10) (by norm_num) (by norm_num) ha2582.le hb2586 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2594/10) with hb2590 | ha2590
  · exact rv_piece n (2590/10) (2594/10) (by norm_num) (by norm_num) ha2586.le hb2590 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2598/10) with hb2594 | ha2594
  · exact rv_piece n (2594/10) (2598/10) (by norm_num) (by norm_num) ha2590.le hb2594 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2602/10) with hb2598 | ha2598
  · exact rv_piece n (2598/10) (2602/10) (by norm_num) (by norm_num) ha2594.le hb2598 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2606/10) with hb2602 | ha2602
  · exact rv_piece n (2602/10) (2606/10) (by norm_num) (by norm_num) ha2598.le hb2602 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2610/10) with hb2606 | ha2606
  · exact rv_piece n (2606/10) (2610/10) (by norm_num) (by norm_num) ha2602.le hb2606 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2614/10) with hb2610 | ha2610
  · exact rv_piece n (2610/10) (2614/10) (by norm_num) (by norm_num) ha2606.le hb2610 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2618/10) with hb2614 | ha2614
  · exact rv_piece n (2614/10) (2618/10) (by norm_num) (by norm_num) ha2610.le hb2614 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2622/10) with hb2618 | ha2618
  · exact rv_piece n (2618/10) (2622/10) (by norm_num) (by norm_num) ha2614.le hb2618 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2626/10) with hb2622 | ha2622
  · exact rv_piece n (2622/10) (2626/10) (by norm_num) (by norm_num) ha2618.le hb2622 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2630/10) with hb2626 | ha2626
  · exact rv_piece n (2626/10) (2630/10) (by norm_num) (by norm_num) ha2622.le hb2626 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2634/10) with hb2630 | ha2630
  · exact rv_piece n (2630/10) (2634/10) (by norm_num) (by norm_num) ha2626.le hb2630 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2638/10) with hb2634 | ha2634
  · exact rv_piece n (2634/10) (2638/10) (by norm_num) (by norm_num) ha2630.le hb2634 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2642/10) with hb2638 | ha2638
  · exact rv_piece n (2638/10) (2642/10) (by norm_num) (by norm_num) ha2634.le hb2638 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2646/10) with hb2642 | ha2642
  · exact rv_piece n (2642/10) (2646/10) (by norm_num) (by norm_num) ha2638.le hb2642 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2650/10) with hb2646 | ha2646
  · exact rv_piece n (2646/10) (2650/10) (by norm_num) (by norm_num) ha2642.le hb2646 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2654/10) with hb2650 | ha2650
  · exact rv_piece n (2650/10) (2654/10) (by norm_num) (by norm_num) ha2646.le hb2650 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2658/10) with hb2654 | ha2654
  · exact rv_piece n (2654/10) (2658/10) (by norm_num) (by norm_num) ha2650.le hb2654 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2662/10) with hb2658 | ha2658
  · exact rv_piece n (2658/10) (2662/10) (by norm_num) (by norm_num) ha2654.le hb2658 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2666/10) with hb2662 | ha2662
  · exact rv_piece n (2662/10) (2666/10) (by norm_num) (by norm_num) ha2658.le hb2662 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2670/10) with hb2666 | ha2666
  · exact rv_piece n (2666/10) (2670/10) (by norm_num) (by norm_num) ha2662.le hb2666 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2674/10) with hb2670 | ha2670
  · exact rv_piece n (2670/10) (2674/10) (by norm_num) (by norm_num) ha2666.le hb2670 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2678/10) with hb2674 | ha2674
  · exact rv_piece n (2674/10) (2678/10) (by norm_num) (by norm_num) ha2670.le hb2674 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2682/10) with hb2678 | ha2678
  · exact rv_piece n (2678/10) (2682/10) (by norm_num) (by norm_num) ha2674.le hb2678 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2686/10) with hb2682 | ha2682
  · exact rv_piece n (2682/10) (2686/10) (by norm_num) (by norm_num) ha2678.le hb2682 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2690/10) with hb2686 | ha2686
  · exact rv_piece n (2686/10) (2690/10) (by norm_num) (by norm_num) ha2682.le hb2686 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2694/10) with hb2690 | ha2690
  · exact rv_piece n (2690/10) (2694/10) (by norm_num) (by norm_num) ha2686.le hb2690 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2698/10) with hb2694 | ha2694
  · exact rv_piece n (2694/10) (2698/10) (by norm_num) (by norm_num) ha2690.le hb2694 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2702/10) with hb2698 | ha2698
  · exact rv_piece n (2698/10) (2702/10) (by norm_num) (by norm_num) ha2694.le hb2698 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2706/10) with hb2702 | ha2702
  · exact rv_piece n (2702/10) (2706/10) (by norm_num) (by norm_num) ha2698.le hb2702 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2710/10) with hb2706 | ha2706
  · exact rv_piece n (2706/10) (2710/10) (by norm_num) (by norm_num) ha2702.le hb2706 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2713/10) with hb2710 | ha2710
  · exact rv_piece n (2710/10) (2713/10) (by norm_num) (by norm_num) ha2706.le hb2710 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2716/10) with hb2713 | ha2713
  · exact rv_piece n (2713/10) (2716/10) (by norm_num) (by norm_num) ha2710.le hb2713 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2719/10) with hb2716 | ha2716
  · exact rv_piece n (2716/10) (2719/10) (by norm_num) (by norm_num) ha2713.le hb2716 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2722/10) with hb2719 | ha2719
  · exact rv_piece n (2719/10) (2722/10) (by norm_num) (by norm_num) ha2716.le hb2719 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2725/10) with hb2722 | ha2722
  · exact rv_piece n (2722/10) (2725/10) (by norm_num) (by norm_num) ha2719.le hb2722 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2728/10) with hb2725 | ha2725
  · exact rv_piece n (2725/10) (2728/10) (by norm_num) (by norm_num) ha2722.le hb2725 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2731/10) with hb2728 | ha2728
  · exact rv_piece n (2728/10) (2731/10) (by norm_num) (by norm_num) ha2725.le hb2728 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2734/10) with hb2731 | ha2731
  · exact rv_piece n (2731/10) (2734/10) (by norm_num) (by norm_num) ha2728.le hb2731 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2737/10) with hb2734 | ha2734
  · exact rv_piece n (2734/10) (2737/10) (by norm_num) (by norm_num) ha2731.le hb2734 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2740/10) with hb2737 | ha2737
  · exact rv_piece n (2737/10) (2740/10) (by norm_num) (by norm_num) ha2734.le hb2737 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2743/10) with hb2740 | ha2740
  · exact rv_piece n (2740/10) (2743/10) (by norm_num) (by norm_num) ha2737.le hb2740 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2746/10) with hb2743 | ha2743
  · exact rv_piece n (2743/10) (2746/10) (by norm_num) (by norm_num) ha2740.le hb2743 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2749/10) with hb2746 | ha2746
  · exact rv_piece n (2746/10) (2749/10) (by norm_num) (by norm_num) ha2743.le hb2746 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2752/10) with hb2749 | ha2749
  · exact rv_piece n (2749/10) (2752/10) (by norm_num) (by norm_num) ha2746.le hb2749 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2755/10) with hb2752 | ha2752
  · exact rv_piece n (2752/10) (2755/10) (by norm_num) (by norm_num) ha2749.le hb2752 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2758/10) with hb2755 | ha2755
  · exact rv_piece n (2755/10) (2758/10) (by norm_num) (by norm_num) ha2752.le hb2755 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2761/10) with hb2758 | ha2758
  · exact rv_piece n (2758/10) (2761/10) (by norm_num) (by norm_num) ha2755.le hb2758 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2764/10) with hb2761 | ha2761
  · exact rv_piece n (2761/10) (2764/10) (by norm_num) (by norm_num) ha2758.le hb2761 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2767/10) with hb2764 | ha2764
  · exact rv_piece n (2764/10) (2767/10) (by norm_num) (by norm_num) ha2761.le hb2764 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2770/10) with hb2767 | ha2767
  · exact rv_piece n (2767/10) (2770/10) (by norm_num) (by norm_num) ha2764.le hb2767 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2773/10) with hb2770 | ha2770
  · exact rv_piece n (2770/10) (2773/10) (by norm_num) (by norm_num) ha2767.le hb2770 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2776/10) with hb2773 | ha2773
  · exact rv_piece n (2773/10) (2776/10) (by norm_num) (by norm_num) ha2770.le hb2773 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2779/10) with hb2776 | ha2776
  · exact rv_piece n (2776/10) (2779/10) (by norm_num) (by norm_num) ha2773.le hb2776 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2782/10) with hb2779 | ha2779
  · exact rv_piece n (2779/10) (2782/10) (by norm_num) (by norm_num) ha2776.le hb2779 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2785/10) with hb2782 | ha2782
  · exact rv_piece n (2782/10) (2785/10) (by norm_num) (by norm_num) ha2779.le hb2782 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2788/10) with hb2785 | ha2785
  · exact rv_piece n (2785/10) (2788/10) (by norm_num) (by norm_num) ha2782.le hb2785 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2791/10) with hb2788 | ha2788
  · exact rv_piece n (2788/10) (2791/10) (by norm_num) (by norm_num) ha2785.le hb2788 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2794/10) with hb2791 | ha2791
  · exact rv_piece n (2791/10) (2794/10) (by norm_num) (by norm_num) ha2788.le hb2791 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2797/10) with hb2794 | ha2794
  · exact rv_piece n (2794/10) (2797/10) (by norm_num) (by norm_num) ha2791.le hb2794 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2800/10) with hb2797 | ha2797
  · exact rv_piece n (2797/10) (2800/10) (by norm_num) (by norm_num) ha2794.le hb2797 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2803/10) with hb2800 | ha2800
  · exact rv_piece n (2800/10) (2803/10) (by norm_num) (by norm_num) ha2797.le hb2800 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2806/10) with hb2803 | ha2803
  · exact rv_piece n (2803/10) (2806/10) (by norm_num) (by norm_num) ha2800.le hb2803 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2809/10) with hb2806 | ha2806
  · exact rv_piece n (2806/10) (2809/10) (by norm_num) (by norm_num) ha2803.le hb2806 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2812/10) with hb2809 | ha2809
  · exact rv_piece n (2809/10) (2812/10) (by norm_num) (by norm_num) ha2806.le hb2809 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2815/10) with hb2812 | ha2812
  · exact rv_piece n (2812/10) (2815/10) (by norm_num) (by norm_num) ha2809.le hb2812 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2818/10) with hb2815 | ha2815
  · exact rv_piece n (2815/10) (2818/10) (by norm_num) (by norm_num) ha2812.le hb2815 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2821/10) with hb2818 | ha2818
  · exact rv_piece n (2818/10) (2821/10) (by norm_num) (by norm_num) ha2815.le hb2818 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2824/10) with hb2821 | ha2821
  · exact rv_piece n (2821/10) (2824/10) (by norm_num) (by norm_num) ha2818.le hb2821 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2827/10) with hb2824 | ha2824
  · exact rv_piece n (2824/10) (2827/10) (by norm_num) (by norm_num) ha2821.le hb2824 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2830/10) with hb2827 | ha2827
  · exact rv_piece n (2827/10) (2830/10) (by norm_num) (by norm_num) ha2824.le hb2827 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2833/10) with hb2830 | ha2830
  · exact rv_piece n (2830/10) (2833/10) (by norm_num) (by norm_num) ha2827.le hb2830 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2836/10) with hb2833 | ha2833
  · exact rv_piece n (2833/10) (2836/10) (by norm_num) (by norm_num) ha2830.le hb2833 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2839/10) with hb2836 | ha2836
  · exact rv_piece n (2836/10) (2839/10) (by norm_num) (by norm_num) ha2833.le hb2836 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2842/10) with hb2839 | ha2839
  · exact rv_piece n (2839/10) (2842/10) (by norm_num) (by norm_num) ha2836.le hb2839 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2845/10) with hb2842 | ha2842
  · exact rv_piece n (2842/10) (2845/10) (by norm_num) (by norm_num) ha2839.le hb2842 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2848/10) with hb2845 | ha2845
  · exact rv_piece n (2845/10) (2848/10) (by norm_num) (by norm_num) ha2842.le hb2845 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2851/10) with hb2848 | ha2848
  · exact rv_piece n (2848/10) (2851/10) (by norm_num) (by norm_num) ha2845.le hb2848 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2854/10) with hb2851 | ha2851
  · exact rv_piece n (2851/10) (2854/10) (by norm_num) (by norm_num) ha2848.le hb2851 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2857/10) with hb2854 | ha2854
  · exact rv_piece n (2854/10) (2857/10) (by norm_num) (by norm_num) ha2851.le hb2854 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2860/10) with hb2857 | ha2857
  · exact rv_piece n (2857/10) (2860/10) (by norm_num) (by norm_num) ha2854.le hb2857 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2863/10) with hb2860 | ha2860
  · exact rv_piece n (2860/10) (2863/10) (by norm_num) (by norm_num) ha2857.le hb2860 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2866/10) with hb2863 | ha2863
  · exact rv_piece n (2863/10) (2866/10) (by norm_num) (by norm_num) ha2860.le hb2863 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2869/10) with hb2866 | ha2866
  · exact rv_piece n (2866/10) (2869/10) (by norm_num) (by norm_num) ha2863.le hb2866 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2872/10) with hb2869 | ha2869
  · exact rv_piece n (2869/10) (2872/10) (by norm_num) (by norm_num) ha2866.le hb2869 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2875/10) with hb2872 | ha2872
  · exact rv_piece n (2872/10) (2875/10) (by norm_num) (by norm_num) ha2869.le hb2872 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2878/10) with hb2875 | ha2875
  · exact rv_piece n (2875/10) (2878/10) (by norm_num) (by norm_num) ha2872.le hb2875 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2881/10) with hb2878 | ha2878
  · exact rv_piece n (2878/10) (2881/10) (by norm_num) (by norm_num) ha2875.le hb2878 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2884/10) with hb2881 | ha2881
  · exact rv_piece n (2881/10) (2884/10) (by norm_num) (by norm_num) ha2878.le hb2881 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2886/10) with hb2884 | ha2884
  · exact rv_piece n (2884/10) (2886/10) (by norm_num) (by norm_num) ha2881.le hb2884 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2888/10) with hb2886 | ha2886
  · exact rv_piece n (2886/10) (2888/10) (by norm_num) (by norm_num) ha2884.le hb2886 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2890/10) with hb2888 | ha2888
  · exact rv_piece n (2888/10) (2890/10) (by norm_num) (by norm_num) ha2886.le hb2888 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2892/10) with hb2890 | ha2890
  · exact rv_piece n (2890/10) (2892/10) (by norm_num) (by norm_num) ha2888.le hb2890 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2894/10) with hb2892 | ha2892
  · exact rv_piece n (2892/10) (2894/10) (by norm_num) (by norm_num) ha2890.le hb2892 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2896/10) with hb2894 | ha2894
  · exact rv_piece n (2894/10) (2896/10) (by norm_num) (by norm_num) ha2892.le hb2894 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2898/10) with hb2896 | ha2896
  · exact rv_piece n (2896/10) (2898/10) (by norm_num) (by norm_num) ha2894.le hb2896 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2900/10) with hb2898 | ha2898
  · exact rv_piece n (2898/10) (2900/10) (by norm_num) (by norm_num) ha2896.le hb2898 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2902/10) with hb2900 | ha2900
  · exact rv_piece n (2900/10) (2902/10) (by norm_num) (by norm_num) ha2898.le hb2900 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2904/10) with hb2902 | ha2902
  · exact rv_piece n (2902/10) (2904/10) (by norm_num) (by norm_num) ha2900.le hb2902 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2906/10) with hb2904 | ha2904
  · exact rv_piece n (2904/10) (2906/10) (by norm_num) (by norm_num) ha2902.le hb2904 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2908/10) with hb2906 | ha2906
  · exact rv_piece n (2906/10) (2908/10) (by norm_num) (by norm_num) ha2904.le hb2906 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2910/10) with hb2908 | ha2908
  · exact rv_piece n (2908/10) (2910/10) (by norm_num) (by norm_num) ha2906.le hb2908 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2912/10) with hb2910 | ha2910
  · exact rv_piece n (2910/10) (2912/10) (by norm_num) (by norm_num) ha2908.le hb2910 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2914/10) with hb2912 | ha2912
  · exact rv_piece n (2912/10) (2914/10) (by norm_num) (by norm_num) ha2910.le hb2912 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2916/10) with hb2914 | ha2914
  · exact rv_piece n (2914/10) (2916/10) (by norm_num) (by norm_num) ha2912.le hb2914 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2918/10) with hb2916 | ha2916
  · exact rv_piece n (2916/10) (2918/10) (by norm_num) (by norm_num) ha2914.le hb2916 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2920/10) with hb2918 | ha2918
  · exact rv_piece n (2918/10) (2920/10) (by norm_num) (by norm_num) ha2916.le hb2918 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2922/10) with hb2920 | ha2920
  · exact rv_piece n (2920/10) (2922/10) (by norm_num) (by norm_num) ha2918.le hb2920 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2924/10) with hb2922 | ha2922
  · exact rv_piece n (2922/10) (2924/10) (by norm_num) (by norm_num) ha2920.le hb2922 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2926/10) with hb2924 | ha2924
  · exact rv_piece n (2924/10) (2926/10) (by norm_num) (by norm_num) ha2922.le hb2924 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2928/10) with hb2926 | ha2926
  · exact rv_piece n (2926/10) (2928/10) (by norm_num) (by norm_num) ha2924.le hb2926 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2930/10) with hb2928 | ha2928
  · exact rv_piece n (2928/10) (2930/10) (by norm_num) (by norm_num) ha2926.le hb2928 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2932/10) with hb2930 | ha2930
  · exact rv_piece n (2930/10) (2932/10) (by norm_num) (by norm_num) ha2928.le hb2930 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2934/10) with hb2932 | ha2932
  · exact rv_piece n (2932/10) (2934/10) (by norm_num) (by norm_num) ha2930.le hb2932 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2936/10) with hb2934 | ha2934
  · exact rv_piece n (2934/10) (2936/10) (by norm_num) (by norm_num) ha2932.le hb2934 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2938/10) with hb2936 | ha2936
  · exact rv_piece n (2936/10) (2938/10) (by norm_num) (by norm_num) ha2934.le hb2936 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2940/10) with hb2938 | ha2938
  · exact rv_piece n (2938/10) (2940/10) (by norm_num) (by norm_num) ha2936.le hb2938 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2942/10) with hb2940 | ha2940
  · exact rv_piece n (2940/10) (2942/10) (by norm_num) (by norm_num) ha2938.le hb2940 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2944/10) with hb2942 | ha2942
  · exact rv_piece n (2942/10) (2944/10) (by norm_num) (by norm_num) ha2940.le hb2942 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2946/10) with hb2944 | ha2944
  · exact rv_piece n (2944/10) (2946/10) (by norm_num) (by norm_num) ha2942.le hb2944 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2948/10) with hb2946 | ha2946
  · exact rv_piece n (2946/10) (2948/10) (by norm_num) (by norm_num) ha2944.le hb2946 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2950/10) with hb2948 | ha2948
  · exact rv_piece n (2948/10) (2950/10) (by norm_num) (by norm_num) ha2946.le hb2948 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2952/10) with hb2950 | ha2950
  · exact rv_piece n (2950/10) (2952/10) (by norm_num) (by norm_num) ha2948.le hb2950 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2954/10) with hb2952 | ha2952
  · exact rv_piece n (2952/10) (2954/10) (by norm_num) (by norm_num) ha2950.le hb2952 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2956/10) with hb2954 | ha2954
  · exact rv_piece n (2954/10) (2956/10) (by norm_num) (by norm_num) ha2952.le hb2954 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2958/10) with hb2956 | ha2956
  · exact rv_piece n (2956/10) (2958/10) (by norm_num) (by norm_num) ha2954.le hb2956 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2960/10) with hb2958 | ha2958
  · exact rv_piece n (2958/10) (2960/10) (by norm_num) (by norm_num) ha2956.le hb2958 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2962/10) with hb2960 | ha2960
  · exact rv_piece n (2960/10) (2962/10) (by norm_num) (by norm_num) ha2958.le hb2960 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2964/10) with hb2962 | ha2962
  · exact rv_piece n (2962/10) (2964/10) (by norm_num) (by norm_num) ha2960.le hb2962 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2966/10) with hb2964 | ha2964
  · exact rv_piece n (2964/10) (2966/10) (by norm_num) (by norm_num) ha2962.le hb2964 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2968/10) with hb2966 | ha2966
  · exact rv_piece n (2966/10) (2968/10) (by norm_num) (by norm_num) ha2964.le hb2966 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2970/10) with hb2968 | ha2968
  · exact rv_piece n (2968/10) (2970/10) (by norm_num) (by norm_num) ha2966.le hb2968 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2972/10) with hb2970 | ha2970
  · exact rv_piece n (2970/10) (2972/10) (by norm_num) (by norm_num) ha2968.le hb2970 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2974/10) with hb2972 | ha2972
  · exact rv_piece n (2972/10) (2974/10) (by norm_num) (by norm_num) ha2970.le hb2972 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2976/10) with hb2974 | ha2974
  · exact rv_piece n (2974/10) (2976/10) (by norm_num) (by norm_num) ha2972.le hb2974 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2978/10) with hb2976 | ha2976
  · exact rv_piece n (2976/10) (2978/10) (by norm_num) (by norm_num) ha2974.le hb2976 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2980/10) with hb2978 | ha2978
  · exact rv_piece n (2978/10) (2980/10) (by norm_num) (by norm_num) ha2976.le hb2978 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2982/10) with hb2980 | ha2980
  · exact rv_piece n (2980/10) (2982/10) (by norm_num) (by norm_num) ha2978.le hb2980 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2984/10) with hb2982 | ha2982
  · exact rv_piece n (2982/10) (2984/10) (by norm_num) (by norm_num) ha2980.le hb2982 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2986/10) with hb2984 | ha2984
  · exact rv_piece n (2984/10) (2986/10) (by norm_num) (by norm_num) ha2982.le hb2984 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2988/10) with hb2986 | ha2986
  · exact rv_piece n (2986/10) (2988/10) (by norm_num) (by norm_num) ha2984.le hb2986 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2990/10) with hb2988 | ha2988
  · exact rv_piece n (2988/10) (2990/10) (by norm_num) (by norm_num) ha2986.le hb2988 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2992/10) with hb2990 | ha2990
  · exact rv_piece n (2990/10) (2992/10) (by norm_num) (by norm_num) ha2988.le hb2990 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2994/10) with hb2992 | ha2992
  · exact rv_piece n (2992/10) (2994/10) (by norm_num) (by norm_num) ha2990.le hb2992 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2996/10) with hb2994 | ha2994
  · exact rv_piece n (2994/10) (2996/10) (by norm_num) (by norm_num) ha2992.le hb2994 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) (2998/10) with hb2996 | ha2996
  · exact rv_piece n (2996/10) (2998/10) (by norm_num) (by norm_num) ha2994.le hb2996 (by norm_num) (by norm_num)
  exact rv_piece n (2998/10) 300 (by norm_num) (by norm_num) ha2996.le h2 (by norm_num) (by norm_num)

end P27




/-! ## part: Phi -/

open Real


theorem solution (n : ℕ) (h1 : 19 ≤ Real.log n) (h2 : Real.log n ≤ 300) :
    (n : ℝ) * (100 / 1999) ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) := P27.rv_range n h1 h2
#print axioms solution
