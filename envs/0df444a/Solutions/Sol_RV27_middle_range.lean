-- Prove2me | solution 1 for RV27.middle_range
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-06T14:36:35.877719+00:00
-- url     : https://prove2.me/submissions/de0e3352-1dea-42c0-bf16-bd001cb447cd

import Mathlib
import Definitions.Def_Schnir_defs
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate
import Theorems.Thm_TaoFivePrimes_siebert_prime_pair_bound

/-!
Middle range of the `27` argument: for `23 ≤ log n ≤ 300`, at least `n/25` integers `s ≤ n`
are sums of two odd primes.

Riesel–Vaughan small shifts (Ark. Mat. 21 (1983), Lemma 8): with `Q` the first `150` odd primes and
`R(s) = #{a ∈ Q : s - a odd prime}`, Cauchy–Schwarz gives `#{s ≤ n : R(s) > 0} ≥ (∑R)²/∑R²`.
* `∑ R ≥ 150 (π(n - 877) - 1)` and Chebyshev's `ψ(x) ≥ a x - 5 log x + 5`, `a ≈ 0.9212`;
* `∑ R² ≤ ∑ R + 2 ∑_{b<a} #{prime pairs (m, m + a - b)}`, each bounded by the platform's
  `TaoFivePrimes.siebert_prime_pair_bound` (`8 C K(d) n / log² n`), with
  `∑_{b<a} K(a-b) ≤ 19496` (`K(d) = ∏_{p ∣ d, p > 2} (p-1)/(p-2)`) checked by the kernel.
The range is split into `56` pieces `La ≤ log n ≤ Lb`.
-/

-- ===== Cheb =====
/-! Chebyshev's lower bound `ψ(x) ≥ a x - 5 log x + 5` for `x ≥ 30`, `a ≈ 0.92129`
(ported from PrimeNumberTheoremAnd, `IEANTN/Chebyshev.lean`, with explicit `log 3`, `log 5` bounds). -/

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

-- ===== Base =====
/-! The singular-series weight `K(s) = ∏_{p ∣ s, p > 2} (p-1)/(p-2)`. -/

namespace P27

noncomputable def Kf (s : ℕ) : ℝ :=
  ∏ p ∈ s.primeFactors, if 2 < p then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1

end P27

-- ===== TSum =====
/-! The small primes `Q` (the first 150 odd primes) and the weight sum `∑_{b<a} K(a-b)`. -/

open Finset Real

namespace P27
def Qc0 : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
def Qc1 : List ℕ := [37, 41, 43, 47, 53, 59, 61, 67, 71, 73]
def Qc2 : List ℕ := [79, 83, 89, 97, 101, 103, 107, 109, 113, 127]
def Qc3 : List ℕ := [131, 137, 139, 149, 151, 157, 163, 167, 173, 179]
def Qc4 : List ℕ := [181, 191, 193, 197, 199, 211, 223, 227, 229, 233]
def Qc5 : List ℕ := [239, 241, 251, 257, 263, 269, 271, 277, 281, 283]
def Qc6 : List ℕ := [293, 307, 311, 313, 317, 331, 337, 347, 349, 353]
def Qc7 : List ℕ := [359, 367, 373, 379, 383, 389, 397, 401, 409, 419]
def Qc8 : List ℕ := [421, 431, 433, 439, 443, 449, 457, 461, 463, 467]
def Qc9 : List ℕ := [479, 487, 491, 499, 503, 509, 521, 523, 541, 547]
def Qc10 : List ℕ := [557, 563, 569, 571, 577, 587, 593, 599, 601, 607]
def Qc11 : List ℕ := [613, 617, 619, 631, 641, 643, 647, 653, 659, 661]
def Qc12 : List ℕ := [673, 677, 683, 691, 701, 709, 719, 727, 733, 739]
def Qc13 : List ℕ := [743, 751, 757, 761, 769, 773, 787, 797, 809, 811]
def Qc14 : List ℕ := [821, 823, 827, 829, 839, 853, 857, 859, 863, 877]
def Qlist : List ℕ := Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14
theorem Qlist_nodup : Qlist.Nodup := by decide +kernel

def Qs : Finset ℕ := ⟨(Qlist : Multiset ℕ), Multiset.coe_nodup.2 Qlist_nodup⟩

theorem Qc0_prime : ∀ p ∈ Qc0, p.Prime := by
  simp only [Qc0, List.forall_mem_cons]
  norm_num

theorem Qc1_prime : ∀ p ∈ Qc1, p.Prime := by
  simp only [Qc1, List.forall_mem_cons]
  norm_num

theorem Qc2_prime : ∀ p ∈ Qc2, p.Prime := by
  simp only [Qc2, List.forall_mem_cons]
  norm_num

theorem Qc3_prime : ∀ p ∈ Qc3, p.Prime := by
  simp only [Qc3, List.forall_mem_cons]
  norm_num

theorem Qc4_prime : ∀ p ∈ Qc4, p.Prime := by
  simp only [Qc4, List.forall_mem_cons]
  norm_num

theorem Qc5_prime : ∀ p ∈ Qc5, p.Prime := by
  simp only [Qc5, List.forall_mem_cons]
  norm_num

theorem Qc6_prime : ∀ p ∈ Qc6, p.Prime := by
  simp only [Qc6, List.forall_mem_cons]
  norm_num

theorem Qc7_prime : ∀ p ∈ Qc7, p.Prime := by
  simp only [Qc7, List.forall_mem_cons]
  norm_num

theorem Qc8_prime : ∀ p ∈ Qc8, p.Prime := by
  simp only [Qc8, List.forall_mem_cons]
  norm_num

theorem Qc9_prime : ∀ p ∈ Qc9, p.Prime := by
  simp only [Qc9, List.forall_mem_cons]
  norm_num

theorem Qc10_prime : ∀ p ∈ Qc10, p.Prime := by
  simp only [Qc10, List.forall_mem_cons]
  norm_num

theorem Qc11_prime : ∀ p ∈ Qc11, p.Prime := by
  simp only [Qc11, List.forall_mem_cons]
  norm_num

theorem Qc12_prime : ∀ p ∈ Qc12, p.Prime := by
  simp only [Qc12, List.forall_mem_cons]
  norm_num

theorem Qc13_prime : ∀ p ∈ Qc13, p.Prime := by
  simp only [Qc13, List.forall_mem_cons]
  norm_num

theorem Qc14_prime : ∀ p ∈ Qc14, p.Prime := by
  simp only [Qc14, List.forall_mem_cons]
  norm_num

theorem Qlist_prime : ∀ p ∈ Qlist, p.Prime :=
  List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨Qc0_prime, Qc1_prime⟩, Qc2_prime⟩, Qc3_prime⟩, Qc4_prime⟩, Qc5_prime⟩, Qc6_prime⟩, Qc7_prime⟩, Qc8_prime⟩, Qc9_prime⟩, Qc10_prime⟩, Qc11_prime⟩, Qc12_prime⟩, Qc13_prime⟩, Qc14_prime⟩

theorem Qs_prop (p : ℕ) (hp : p ∈ Qs) : p.Prime ∧ p ≠ 2 ∧ p ≤ 877 := by
  have hp' : p ∈ Qlist := Multiset.mem_coe.1 (Finset.mem_def.1 hp)
  refine ⟨Qlist_prime p hp', ?_, ?_⟩
  · have : ∀ q ∈ Qlist, q ≠ 2 := by decide +kernel
    exact this p hp'
  · have : ∀ q ∈ Qlist, q ≤ 877 := by decide +kernel
    exact this p hp'

theorem Qs_card : Qs.card = 150 := by decide +kernel

def Sset : Finset ℕ := {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43}

def Wk (d : ℕ) : ℕ := ∏ p ∈ Sset, (if p ∣ d then p - 1 else p - 2)

def Dk : ℕ := ∏ p ∈ Sset, (p - 2)

theorem Sset_prime : ∀ p ∈ Sset, p.Prime ∧ 3 ≤ p := by
  intro p hp
  simp only [Sset, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

noncomputable def fK (p : ℕ) : ℝ := ((p : ℝ) - 1) / ((p : ℝ) - 2)

theorem one_le_fK (p : ℕ) (hp : 3 ≤ p) : 1 ≤ fK p := by
  unfold fK
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  rw [le_div_iff₀ (by linarith)]; linarith

theorem fK_le_47 (p : ℕ) (hp : 47 ≤ p) : fK p ≤ 46 / 45 := by
  unfold fK
  have h : (47 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

theorem fK_term (p d : ℕ) (hp : 3 ≤ p) :
    (if p ∣ d then fK p else 1) =
      (((if p ∣ d then p - 1 else p - 2 : ℕ) : ℝ) / (((p - 2 : ℕ)) : ℝ)) := by
  have hc1 : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hc2 : (((p - 2 : ℕ)) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hne : (p : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  split_ifs
  · unfold fK; push_cast [hc1, hc2]; rfl
  · push_cast [hc2]; rw [div_self hne]

theorem prod_S_eq (d : ℕ) :
    ∏ p ∈ Sset, (if p ∣ d then fK p else 1) = (Wk d : ℝ) / Dk := by
  rw [prod_congr rfl (fun p hp => fK_term p d (Sset_prime p hp).2), prod_div_distrib]
  unfold Wk Dk
  rw [Nat.cast_prod, Nat.cast_prod]

set_option maxHeartbeats 1000000 in
theorem Kf_le_Wk (d : ℕ) (hd0 : 0 < d) (hdl : d < 2209) :
    Kf d ≤ 46 / 45 * (Wk d : ℝ) / Dk := by
  have hKf : Kf d = ∏ p ∈ d.primeFactors, (if 2 < p then fK p else 1) := rfl
  rw [hKf, ← prod_filter_mul_prod_filter_not d.primeFactors (fun p => p < 47)]
  have hsmall : d.primeFactors.filter (fun p => p < 47) = (insert 2 Sset).filter (fun p => p ∣ d) := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors, mem_insert]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hp47⟩
      refine ⟨?_, hpd⟩
      have := hpp.two_le
      interval_cases p <;> first | (left; rfl) | (right; decide) | (exfalso; norm_num at hpp)
    · rintro ⟨hp, hpd⟩
      rcases hp with rfl | hp
      · exact ⟨⟨Nat.prime_two, hpd, by omega⟩, by norm_num⟩
      · refine ⟨⟨(Sset_prime p hp).1, hpd, by omega⟩, ?_⟩
        simp only [Sset, mem_insert, mem_singleton] at hp
        omega
  have h2S : (2 : ℕ) ∉ Sset := by decide
  rw [hsmall, prod_filter, prod_insert h2S]
  have hS : ∏ p ∈ Sset, (if p ∣ d then (if 2 < p then fK p else 1) else 1) =
      ∏ p ∈ Sset, (if p ∣ d then fK p else 1) := by
    refine prod_congr rfl fun p hp => ?_
    have := (Sset_prime p hp).2
    rw [if_pos (show 2 < p by omega)]
  rw [hS, prod_S_eq]
  have h2 : (if 2 ∣ d then (if 2 < 2 then fK 2 else 1) else 1) = (1 : ℝ) := by simp
  rw [h2, one_mul]
  set Bf := d.primeFactors.filter (fun p => ¬ p < 47) with hBf
  have hcard : Bf.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hBf, mem_filter, Nat.mem_primeFactors] at ha hb
    by_contra hab
    have hcop : Nat.Coprime a b := (Nat.coprime_primes ha.1.1 hb.1.1).2 hab
    have hdiv : a * b ∣ d := hcop.mul_dvd_of_dvd_of_dvd ha.1.2.1 hb.1.2.1
    have hle := Nat.le_of_dvd hd0 hdiv
    have ha47 : 47 ≤ a := by omega
    have hb47 : 47 ≤ b := by omega
    have : 47 * 47 ≤ a * b := Nat.mul_le_mul ha47 hb47
    omega
  have hB : ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ 46 / 45 := by
    calc ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ ∏ p ∈ Bf, (46 / 45 : ℝ) := by
          apply prod_le_prod
          · intro p hp
            simp only [hBf, mem_filter] at hp
            rw [if_pos (by omega)]; linarith [one_le_fK p (by omega)]
          · intro p hp
            simp only [hBf, mem_filter] at hp
            rw [if_pos (by omega)]; exact fK_le_47 p (by omega)
      _ = (46 / 45) ^ Bf.card := by rw [prod_const]
      _ ≤ (46 / 45) ^ 1 := pow_le_pow_right₀ (by norm_num) hcard
      _ = 46 / 45 := pow_one _
  have hW : (0 : ℝ) ≤ (Wk d : ℝ) / Dk := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc ((Wk d : ℝ) / Dk) * ∏ p ∈ Bf, (if 2 < p then fK p else 1) ≤ ((Wk d : ℝ) / Dk) * (46 / 45) :=
        mul_le_mul_of_nonneg_left hB hW
    _ = 46 / 45 * (Wk d : ℝ) / Dk := by ring

def Wk2 (d : ℕ) : ℕ := (if d % 3 = 0 then 2 else 1) * (if d % 5 = 0 then 4 else 3) * (if d % 7 = 0 then 6 else 5) * (if d % 11 = 0 then 10 else 9) * (if d % 13 = 0 then 12 else 11) * (if d % 17 = 0 then 16 else 15) * (if d % 19 = 0 then 18 else 17) * (if d % 23 = 0 then 22 else 21) * (if d % 29 = 0 then 28 else 27) * (if d % 31 = 0 then 30 else 29) * (if d % 37 = 0 then 36 else 35) * (if d % 41 = 0 then 40 else 39) * (if d % 43 = 0 then 42 else 41)

theorem Wk_eq (d : ℕ) : Wk d = Wk2 d := by
  simp only [Wk, Sset, Wk2]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_singleton]
  simp only [Nat.dvd_iff_mod_eq_zero]
  norm_num only [mul_assoc]

def rowW (a : ℕ) : ℕ := (Qlist.map fun b => if b < a then Wk2 (a - b) else 0).sum
theorem chunk0 : (Qc0.map rowW).sum ≤ 22334401544323050 := by decide +kernel
theorem chunk1 : (Qc1.map rowW).sum ≤ 81184428911190150 := by decide +kernel
theorem chunk2 : (Qc2.map rowW).sum ≤ 140965406992975950 := by decide +kernel
theorem chunk3 : (Qc3.map rowW).sum ≤ 201870775876366800 := by decide +kernel
theorem chunk4 : (Qc4.map rowW).sum ≤ 260284136341434975 := by decide +kernel
theorem chunk5 : (Qc5.map rowW).sum ≤ 323231843728747800 := by decide +kernel
theorem chunk6 : (Qc6.map rowW).sum ≤ 383210746492869540 := by decide +kernel
theorem chunk7 : (Qc7.map rowW).sum ≤ 441685524908464515 := by decide +kernel
theorem chunk8 : (Qc8.map rowW).sum ≤ 502604899649725320 := by decide +kernel
theorem chunk9 : (Qc9.map rowW).sum ≤ 563874701075903070 := by decide +kernel
theorem chunk10 : (Qc10.map rowW).sum ≤ 626127811285855725 := by decide +kernel
theorem chunk11 : (Qc11.map rowW).sum ≤ 683907388954790490 := by decide +kernel
theorem chunk12 : (Qc12.map rowW).sum ≤ 742991985680191380 := by decide +kernel
theorem chunk13 : (Qc13.map rowW).sum ≤ 805695899866849530 := by decide +kernel
theorem chunk14 : (Qc14.map rowW).sum ≤ 865807107315140655 := by decide +kernel

theorem sum_Qs {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∑ a ∈ Qs, f a = (Qlist.map f).sum := by
  show Multiset.sum (Multiset.map f (Qlist : Multiset ℕ)) = _
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem Qlist_eq : Qlist = Qc0 ++ Qc1 ++ Qc2 ++ Qc3 ++ Qc4 ++ Qc5 ++ Qc6 ++ Qc7 ++ Qc8 ++ Qc9 ++ Qc10 ++ Qc11 ++ Qc12 ++ Qc13 ++ Qc14 := rfl

theorem row_eq (a : ℕ) : (∑ b ∈ Qs, if b < a then Wk (a - b) else 0) = rowW a := by
  rw [sum_Qs]
  simp only [Wk_eq, rowW]

theorem half_le : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0) ≤ 6645777058624828950 := by
  have h1 : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0) = (Qlist.map rowW).sum := by
    rw [sum_Qs]
    simp only [row_eq]
  rw [h1, Qlist_eq]
  simp only [List.map_append, List.sum_append]
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (chunk0) chunk1) chunk2) chunk3) chunk4) chunk5) chunk6) chunk7) chunk8) chunk9) chunk10) chunk11) chunk12) chunk13) chunk14).trans_eq (by norm_num)

theorem Dk_eq : Dk = 348469040044125 := by
  simp [Dk, Sset]

theorem T_bound :
    ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) ≤ 19496 := by
  have hterm : ∀ a ∈ Qs, ∀ b ∈ Qs, (if b < a then Kf (a - b) else 0) ≤
      46 / 45 / Dk * ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) := by
    intro a ha b hb
    obtain ⟨-, -, ha1⟩ := Qs_prop a ha
    split_ifs with hab
    · have := Kf_le_Wk (a - b) (by omega) (by omega)
      exact this.trans_eq (by ring)
    · simp
  have hD : (0 : ℝ) < Dk := by
    rw [Dk_eq]; norm_num
  have hk : 0 ≤ 46 / 45 / (Dk : ℝ) := div_nonneg (by norm_num) hD.le
  set H := (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then Wk (a - b) else 0 : ℕ) with hH
  have hHle : (H : ℝ) ≤ 6645777058624828950 := by exact_mod_cast half_le
  have hcast : ((H : ℕ) : ℝ) = ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) := by
    rw [hH, Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
  calc ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0)
      ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, 46 / 45 / Dk * ((if b < a then Wk (a - b) else 0 : ℕ) : ℝ) :=
        sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
    _ = 46 / 45 / Dk * (H : ℝ) := by
        rw [hcast, mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
    _ ≤ 46 / 45 / Dk * (6645777058624828950 : ℝ) := mul_le_mul_of_nonneg_left hHle hk
    _ ≤ 19496 := by
        rw [Dk_eq]; norm_num

theorem pairs_card : (∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then 1 else 0 : ℕ) = 11175 := by
  decide +kernel

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

/-- first moment: each `a ∈ Q` contributes at least the odd primes up to `n - 877`. -/
theorem sumR_lower (n : ℕ) (hn : 879 ≤ n) :
    150 * (oddP (n - 877)).card ≤ ∑ s ∈ range (n + 1), Rr s := by
  simp_rw [Rr_eq]
  rw [sum_comm]
  have h : ∀ a ∈ Qs, (oddP (n - 877)).card ≤ ∑ s ∈ range (n + 1), ind a s := by
    intro a ha
    obtain ⟨-, -, ha877⟩ := Qs_prop a ha
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
  calc 150 * (oddP (n - 877)).card = ∑ _a ∈ Qs, (oddP (n - 877)).card := by
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

theorem exp99_ge (x : ℝ) (hx : 70 ≤ x) : (10 : ℝ) ^ 9 ≤ exp x := by
  have h3 : (3 : ℝ) ≤ exp 2 := by linarith [add_one_le_exp (2 : ℝ)]
  have h : exp 70 = exp 2 ^ 35 := by rw [← exp_nat_mul]; norm_num
  calc (10 : ℝ) ^ 9 ≤ 3 ^ 35 := by norm_num
    _ ≤ exp 2 ^ 35 := pow_le_pow_left₀ (by norm_num) h3 35
    _ = exp 70 := h.symm
    _ ≤ exp x := exp_le_exp.2 hx

/-- first moment, from Chebyshev's `ψ(m) ≥ a m - 5 log m + 5` (`a ≥ 0.9212`). -/
theorem X_lower (n : ℕ) (Lb : ℝ) (hn : (10 : ℝ) ^ 9 ≤ n) (hLb : log n ≤ Lb) (hLb12 : Lb ≤ 12000) :
    150 * 0.9211 / Lb * n ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
  have hn879 : 879 ≤ n := by exact_mod_cast (show (879 : ℝ) ≤ n by linarith)
  set m := n - 877 with hm
  have hmR : (m : ℝ) = n - 877 := by rw [hm, Nat.cast_sub (by omega)]; norm_num
  have hX := sumR_lower n hn879
  have hP := oddP_card m (by omega)
  have hpsi1 := Chebyshev.psi_le_primeCounting_mul_log m
  have hpsi2 := Chebyshev.psi_lower (m : ℝ) (by rw [hmR]; linarith)
  have ha := Chebyshev.a_bound.1
  have hm0 : (0 : ℝ) < m := by rw [hmR]; linarith
  have hlogm : log m ≤ log n := log_le_log hm0 (by rw [hmR]; linarith)
  have hlogm0 : 0 < log (m : ℝ) := log_pos (by rw [hmR]; linarith)
  have hc : ((oddP m).card : ℝ) + 1 = Nat.primeCounting m := by exact_mod_cast hP
  have e1 : ((oddP m).card : ℝ) * log m = (Nat.primeCounting m : ℝ) * log m - log m := by
    rw [← hc]; ring
  have key : Chebyshev.a * (m : ℝ) - 6 * log m + 5 ≤ ((oddP m).card : ℝ) * log m := by
    rw [e1]; linarith
  have hcard0 : (0 : ℝ) ≤ (oddP m).card := Nat.cast_nonneg _
  have hk2 : ((oddP m).card : ℝ) * log m ≤ ((oddP m).card : ℝ) * Lb :=
    mul_le_mul_of_nonneg_left (hlogm.trans hLb) hcard0
  have hlogm12 : log (m : ℝ) ≤ 12000 := hlogm.trans (hLb.trans hLb12)
  have hma : Chebyshev.a * (m : ℝ) ≥ 0.9212 * m := mul_le_mul_of_nonneg_right ha hm0.le
  have hmain : 0.9211 * (n : ℝ) ≤ ((oddP m).card : ℝ) * Lb := by
    linarith
  have hLbpos : 0 < Lb := lt_of_lt_of_le (log_pos (by linarith)) hLb
  have hXc : (150 : ℝ) * (oddP m).card ≤ ((∑ s ∈ range (n + 1), Rr s : ℕ) : ℝ) := by
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
theorem off_le (n : ℕ) (La : ℝ) (hLa : 23 ≤ La) (h1 : La ≤ log n) :
    ((2 * ∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) ≤
      n * (16 * 1.3217 * 19496 / La ^ 2) := by
  obtain ⟨-, hCup, -, -⟩ := PrimePairSieve.sieve_constants_certificate
  have hC0 : 0 ≤ TaoFivePrimes.twinPrimeConstant := by
    obtain ⟨h, -⟩ := PrimePairSieve.sieve_constants_certificate; linarith
  have hL : 23 ≤ log (n : ℝ) := hLa.trans h1
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
      w * 19496 := by
    have hcast : ((∑ a ∈ Qs, ∑ b ∈ Qs, if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) =
        ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]; exact sum_congr rfl fun a _ => Nat.cast_sum _ _
    rw [hcast]
    calc ∑ a ∈ Qs, ∑ b ∈ Qs, ((if b < a then PPs (a - b) n else 0 : ℕ) : ℝ)
        ≤ ∑ a ∈ Qs, ∑ b ∈ Qs, w * (if b < a then Kf (a - b) else 0) :=
          sum_le_sum fun a ha => sum_le_sum fun b hb => hterm a ha b hb
      _ = w * ∑ a ∈ Qs, ∑ b ∈ Qs, (if b < a then Kf (a - b) else 0) := by
          rw [mul_sum]; exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
      _ ≤ w * 19496 := mul_le_mul_of_nonneg_left T_bound hw0
  have hwle : w ≤ 8 * 1.3217 * n / La ^ 2 := by
    rw [hw]
    have hLa2 : La ^ 2 ≤ (log n) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
    calc 8 * TaoFivePrimes.twinPrimeConstant * n / (log n) ^ 2 ≤ 8 * 1.3217 * n / (log n) ^ 2 := by
          gcongr
      _ ≤ 8 * 1.3217 * n / La ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) hLa2
  push_cast at hsum ⊢
  have : 2 * (w * 19496) ≤ n * (16 * 1.3217 * 19496 / La ^ 2) := by
    have e : (n : ℝ) * (16 * 1.3217 * 19496 / La ^ 2) = 2 * (8 * 1.3217 * n / La ^ 2 * 19496) := by ring
    rw [e]; nlinarith
  linarith

/-- one piece of the middle range: `#{s ≤ n : r(s) > 0} ≥ n / 25`. -/
theorem rv_piece (n : ℕ) (La Lb : ℝ) (hLa : 23 ≤ La) (hLb12 : Lb ≤ 12000)
    (h1 : La ≤ log n) (h2 : log n ≤ Lb) (hxb : 1 / 50 ≤ 150 * 0.9211 / Lb)
    (hnum : 150 * 0.9211 / Lb + 16 * 1.3217 * 19496 / La ^ 2 ≤ 25 * (150 * 0.9211 / Lb) ^ 2) :
    (n : ℝ) / 25 ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  have hn12 : (10 : ℝ) ^ 9 ≤ n := by
    have hnpos : (0 : ℝ) < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at h1; simp at h1; linarith
      · exact_mod_cast h
    rw [← exp_log hnpos]
    have h3 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have : (10 : ℝ) ^ 9 ≤ exp 23 := by
      have e : exp 23 = exp 1 ^ 23 := by rw [← exp_nat_mul]; norm_num
      rw [e]
      calc (10 : ℝ) ^ 9 ≤ 2.7 ^ 23 := by norm_num
        _ ≤ exp 1 ^ 23 := pow_le_pow_left₀ (by norm_num) h3 23
    exact this.trans (exp_le_exp.2 (by linarith))
  set x := 150 * 0.9211 / Lb with hx
  set k := 16 * 1.3217 * 19496 / La ^ 2 with hk
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
  have h4 : (cnt : ℝ) * (X + n * k) < n / 25 * (X + n * k) :=
    mul_lt_mul_of_pos_right hcon (by linarith)
  have p1 : 0 ≤ ((X : ℝ) - n * x) * (X + n * x - n / 25) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (n : ℝ) * (2 * x - 1 / 25) := mul_nonneg hn0 (by linarith)
    linarith
  have p2 : 0 ≤ (n : ℝ) ^ 2 * (25 * x ^ 2 - x - k) := mul_nonneg (sq_nonneg _) (by linarith)
  have e : (X : ℝ) ^ 2 - n / 25 * (X + n * k) =
      ((X : ℝ) - n * x) * (X + n * x - n / 25) + (n : ℝ) ^ 2 * (25 * x ^ 2 - x - k) / 25 := by
    ring
  linarith

end P27

-- ===== RVRange =====
/-! The middle range `23 ≤ log n ≤ 300`, split into pieces. -/

open Finset Real

namespace P27
open Schnir

theorem rv_range (n : ℕ) (h1 : 23 ≤ log n) (h2 : log n ≤ 300) :
    (n : ℝ) / 25 ≤ (#{s ∈ range (n + 1) | 0 < r s} : ℝ) := by
  rcases le_or_gt (log (n : ℝ)) 24 with hb0 | ha0
  · exact rv_piece n 23 24 (by norm_num) (by norm_num) h1 hb0 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 25 with hb1 | ha1
  · exact rv_piece n 24 25 (by norm_num) (by norm_num) ha0.le hb1 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 26 with hb2 | ha2
  · exact rv_piece n 25 26 (by norm_num) (by norm_num) ha1.le hb2 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 27 with hb3 | ha3
  · exact rv_piece n 26 27 (by norm_num) (by norm_num) ha2.le hb3 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 28 with hb4 | ha4
  · exact rv_piece n 27 28 (by norm_num) (by norm_num) ha3.le hb4 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 29 with hb5 | ha5
  · exact rv_piece n 28 29 (by norm_num) (by norm_num) ha4.le hb5 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 31 with hb6 | ha6
  · exact rv_piece n 29 31 (by norm_num) (by norm_num) ha5.le hb6 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 33 with hb7 | ha7
  · exact rv_piece n 31 33 (by norm_num) (by norm_num) ha6.le hb7 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 35 with hb8 | ha8
  · exact rv_piece n 33 35 (by norm_num) (by norm_num) ha7.le hb8 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 37 with hb9 | ha9
  · exact rv_piece n 35 37 (by norm_num) (by norm_num) ha8.le hb9 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 39 with hb10 | ha10
  · exact rv_piece n 37 39 (by norm_num) (by norm_num) ha9.le hb10 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 41 with hb11 | ha11
  · exact rv_piece n 39 41 (by norm_num) (by norm_num) ha10.le hb11 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 43 with hb12 | ha12
  · exact rv_piece n 41 43 (by norm_num) (by norm_num) ha11.le hb12 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 45 with hb13 | ha13
  · exact rv_piece n 43 45 (by norm_num) (by norm_num) ha12.le hb13 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 48 with hb14 | ha14
  · exact rv_piece n 45 48 (by norm_num) (by norm_num) ha13.le hb14 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 51 with hb15 | ha15
  · exact rv_piece n 48 51 (by norm_num) (by norm_num) ha14.le hb15 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 54 with hb16 | ha16
  · exact rv_piece n 51 54 (by norm_num) (by norm_num) ha15.le hb16 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 57 with hb17 | ha17
  · exact rv_piece n 54 57 (by norm_num) (by norm_num) ha16.le hb17 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 60 with hb18 | ha18
  · exact rv_piece n 57 60 (by norm_num) (by norm_num) ha17.le hb18 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 63 with hb19 | ha19
  · exact rv_piece n 60 63 (by norm_num) (by norm_num) ha18.le hb19 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 67 with hb20 | ha20
  · exact rv_piece n 63 67 (by norm_num) (by norm_num) ha19.le hb20 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 71 with hb21 | ha21
  · exact rv_piece n 67 71 (by norm_num) (by norm_num) ha20.le hb21 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 75 with hb22 | ha22
  · exact rv_piece n 71 75 (by norm_num) (by norm_num) ha21.le hb22 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 79 with hb23 | ha23
  · exact rv_piece n 75 79 (by norm_num) (by norm_num) ha22.le hb23 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 83 with hb24 | ha24
  · exact rv_piece n 79 83 (by norm_num) (by norm_num) ha23.le hb24 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 88 with hb25 | ha25
  · exact rv_piece n 83 88 (by norm_num) (by norm_num) ha24.le hb25 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 93 with hb26 | ha26
  · exact rv_piece n 88 93 (by norm_num) (by norm_num) ha25.le hb26 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 98 with hb27 | ha27
  · exact rv_piece n 93 98 (by norm_num) (by norm_num) ha26.le hb27 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 103 with hb28 | ha28
  · exact rv_piece n 98 103 (by norm_num) (by norm_num) ha27.le hb28 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 109 with hb29 | ha29
  · exact rv_piece n 103 109 (by norm_num) (by norm_num) ha28.le hb29 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 115 with hb30 | ha30
  · exact rv_piece n 109 115 (by norm_num) (by norm_num) ha29.le hb30 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 121 with hb31 | ha31
  · exact rv_piece n 115 121 (by norm_num) (by norm_num) ha30.le hb31 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 127 with hb32 | ha32
  · exact rv_piece n 121 127 (by norm_num) (by norm_num) ha31.le hb32 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 133 with hb33 | ha33
  · exact rv_piece n 127 133 (by norm_num) (by norm_num) ha32.le hb33 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 140 with hb34 | ha34
  · exact rv_piece n 133 140 (by norm_num) (by norm_num) ha33.le hb34 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 147 with hb35 | ha35
  · exact rv_piece n 140 147 (by norm_num) (by norm_num) ha34.le hb35 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 154 with hb36 | ha36
  · exact rv_piece n 147 154 (by norm_num) (by norm_num) ha35.le hb36 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 161 with hb37 | ha37
  · exact rv_piece n 154 161 (by norm_num) (by norm_num) ha36.le hb37 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 168 with hb38 | ha38
  · exact rv_piece n 161 168 (by norm_num) (by norm_num) ha37.le hb38 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 176 with hb39 | ha39
  · exact rv_piece n 168 176 (by norm_num) (by norm_num) ha38.le hb39 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 184 with hb40 | ha40
  · exact rv_piece n 176 184 (by norm_num) (by norm_num) ha39.le hb40 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 192 with hb41 | ha41
  · exact rv_piece n 184 192 (by norm_num) (by norm_num) ha40.le hb41 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 200 with hb42 | ha42
  · exact rv_piece n 192 200 (by norm_num) (by norm_num) ha41.le hb42 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 208 with hb43 | ha43
  · exact rv_piece n 200 208 (by norm_num) (by norm_num) ha42.le hb43 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 216 with hb44 | ha44
  · exact rv_piece n 208 216 (by norm_num) (by norm_num) ha43.le hb44 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 224 with hb45 | ha45
  · exact rv_piece n 216 224 (by norm_num) (by norm_num) ha44.le hb45 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 232 with hb46 | ha46
  · exact rv_piece n 224 232 (by norm_num) (by norm_num) ha45.le hb46 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 240 with hb47 | ha47
  · exact rv_piece n 232 240 (by norm_num) (by norm_num) ha46.le hb47 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 248 with hb48 | ha48
  · exact rv_piece n 240 248 (by norm_num) (by norm_num) ha47.le hb48 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 256 with hb49 | ha49
  · exact rv_piece n 248 256 (by norm_num) (by norm_num) ha48.le hb49 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 264 with hb50 | ha50
  · exact rv_piece n 256 264 (by norm_num) (by norm_num) ha49.le hb50 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 272 with hb51 | ha51
  · exact rv_piece n 264 272 (by norm_num) (by norm_num) ha50.le hb51 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 280 with hb52 | ha52
  · exact rv_piece n 272 280 (by norm_num) (by norm_num) ha51.le hb52 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 288 with hb53 | ha53
  · exact rv_piece n 280 288 (by norm_num) (by norm_num) ha52.le hb53 (by norm_num) (by norm_num)
  rcases le_or_gt (log (n : ℝ)) 296 with hb54 | ha54
  · exact rv_piece n 288 296 (by norm_num) (by norm_num) ha53.le hb54 (by norm_num) (by norm_num)
  exact rv_piece n 296 300 (by norm_num) (by norm_num) ha54.le h2 (by norm_num) (by norm_num)

end P27

/-- `#{s ≤ n : r(s) > 0} ≥ n/25` for `23 ≤ log n ≤ 300` (platform theorem `RV27.middle_range`). -/
theorem solution (n : ℕ) (h1 : 23 ≤ Real.log (n : ℝ)) (h2 : Real.log (n : ℝ) ≤ 300) :
    (n : ℝ) / 25 ≤ (((Finset.range (n + 1)).filter (fun s => 0 < Schnir.r s)).card : ℝ) :=
  P27.rv_range n h1 h2
