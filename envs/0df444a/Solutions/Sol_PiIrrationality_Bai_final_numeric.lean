-- Prove2me | solution 1 for PiIrrationality.Bai.final_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T20:09:17.370174+00:00
-- url     : https://prove2.me/submissions/eb93d288-866f-423b-b8cf-4bcf9f2d5237

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
set_option autoImplicit false

namespace BaiLogs

/-- Partial sum `∑_{k<N} 2 y^(2k+1)/(2k+1)` of the series of `log (1+y) - log (1-y)`. -/
noncomputable def atanhPS (y : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * y ^ (2 * k + 1)

lemma atanh_tail (y : ℝ) (hy : |y| < 1) (N : ℕ) :
    |Real.log (1 + y) - Real.log (1 - y) - atanhPS y N| ≤
      2 * |y| ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - |y| ^ 2)) := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hy
  have h1 := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq] at h1
  have h2 : Real.log (1 + y) - Real.log (1 - y) - atanhPS y N =
      ∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1) := by
    unfold atanhPS; rw [← h1]; ring
  rw [h2]
  have ha : 0 ≤ |y| := abs_nonneg y
  have ha2 : |y| ^ 2 < 1 := by nlinarith
  have hN : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  set C : ℝ := 2 * |y| ^ (2 * N + 1) / (2 * (N : ℝ) + 1) with hC
  have hbound : ∀ i : ℕ, ‖(2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖ ≤
      C * (|y| ^ 2) ^ i := by
    intro i
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have e1 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    have e2 : |1 / (2 * ((i + N : ℕ) : ℝ) + 1)| = 1 / (2 * ((i + N : ℕ) : ℝ) + 1) :=
      abs_of_pos (by positivity)
    rw [e1, e2]
    have e3 : |y| ^ (2 * (i + N) + 1) = |y| ^ (2 * N + 1) * (|y| ^ 2) ^ i := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [e3, hC]
    have e4 : 1 / (2 * ((i + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le hN
      push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have e5 : 0 ≤ |y| ^ (2 * N + 1) * (|y| ^ 2) ^ i := by positivity
    calc (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * (|y| ^ (2 * N + 1) * (|y| ^ 2) ^ i)
        ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (|y| ^ (2 * N + 1) * (|y| ^ 2) ^ i) := by
          gcongr
      _ = 2 * |y| ^ (2 * N + 1) / (2 * (N : ℝ) + 1) * (|y| ^ 2) ^ i := by ring
  have hgeo : Summable (fun i : ℕ => C * (|y| ^ 2) ^ i) :=
    (summable_geometric_of_lt_one (by positivity) ha2).mul_left C
  have hsum : Summable (fun i : ℕ =>
      ‖(2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound hgeo
  calc |∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)|
      = ‖∑' i : ℕ, (2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' i : ℕ, ‖(2 : ℝ) * (1 / (2 * ((i + N : ℕ) : ℝ) + 1)) * y ^ (2 * (i + N) + 1)‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' i : ℕ, C * (|y| ^ 2) ^ i := hsum.tsum_le_tsum hbound hgeo
    _ = C * (1 - |y| ^ 2)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) ha2]
    _ = 2 * |y| ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - |y| ^ 2)) := by
        rw [hC]; field_simp


lemma log_approx (q : ℝ) (hq : 0 < q) (N : ℕ) :
    |Real.log q - atanhPS ((q - 1) / (q + 1)) N| ≤
      2 * |(q - 1) / (q + 1)| ^ (2 * N + 1) /
        ((2 * (N : ℝ) + 1) * (1 - |(q - 1) / (q + 1)| ^ 2)) := by
  have hq1 : 0 < q + 1 := by linarith
  have hy : |(q - 1) / (q + 1)| < 1 := by
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hq1]; linarith
    · rw [div_lt_iff₀ hq1]; linarith
  have h := atanh_tail _ hy N
  have hl : Real.log (1 + (q - 1) / (q + 1)) - Real.log (1 - (q - 1) / (q + 1)) = Real.log q := by
    have h1 : (1 + (q - 1) / (q + 1)) ≠ 0 := by
      have : 1 + (q - 1) / (q + 1) = 2 * q / (q + 1) := by field_simp; ring
      rw [this]; positivity
    have h2 : (1 - (q - 1) / (q + 1)) ≠ 0 := by
      have : 1 - (q - 1) / (q + 1) = 2 / (q + 1) := by field_simp; ring
      rw [this]; positivity
    rw [← Real.log_div h1 h2]
    congr 1
    field_simp
    ring
  rw [hl] at h
  exact h

lemma log_bound_mono (a Y : ℝ) (N : ℕ) (ha : 0 ≤ a) (haY : a ≤ Y) (hY : Y < 1) :
    2 * a ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - a ^ 2)) ≤
      2 * Y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - Y ^ 2)) := by
  have hN : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
  have hY0 : 0 ≤ Y := ha.trans haY
  have hY2 : Y ^ 2 < 1 := by nlinarith
  have hd : 0 < (2 * (N : ℝ) + 1) * (1 - Y ^ 2) := mul_pos hN (by linarith)
  apply div_le_div₀ (by positivity) _ hd
  · apply mul_le_mul_of_nonneg_left _ hN.le
    nlinarith
  · have : a ^ (2 * N + 1) ≤ Y ^ (2 * N + 1) := pow_le_pow_left₀ ha haY _
    linarith

lemma log_le_of (q y Y L : ℝ) (N : ℕ) (hq : 0 < q) (hy : y = (q - 1) / (q + 1)) (hY : |y| ≤ Y)
    (hY1 : Y < 1)
    (hL : atanhPS y N + 2 * Y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - Y ^ 2)) ≤ L) :
    Real.log q ≤ L := by
  subst hy
  have h := (abs_le.1 (log_approx q hq N)).2
  have hb := log_bound_mono _ Y N (abs_nonneg _) hY hY1
  linarith

lemma le_log_of (q y Y L : ℝ) (N : ℕ) (hq : 0 < q) (hy : y = (q - 1) / (q + 1)) (hY : |y| ≤ Y)
    (hY1 : Y < 1)
    (hL : L ≤ atanhPS y N - 2 * Y ^ (2 * N + 1) / ((2 * (N : ℝ) + 1) * (1 - Y ^ 2))) :
    L ≤ Real.log q := by
  subst hy
  have h := (abs_le.1 (log_approx q hq N)).1
  have hb := log_bound_mono _ Y N (abs_nonneg _) hY hY1
  linarith


lemma log_two_bounds : (0.69314718055994530941723212 : ℝ) ≤ Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ (0.69314718055994530941723213 : ℝ) := by
  constructor
  · exact le_log_of (2 : ℝ) (1 / 3 : ℝ) (166667 / 500000 : ℝ) _ 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (2 : ℝ) (1 / 3 : ℝ) (166667 / 500000 : ℝ) _ 30 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_five_quarter_bounds : (0.223143551314209755766295090309 : ℝ) ≤ Real.log (5 / 4 : ℝ) ∧ Real.log (5 / 4 : ℝ) ≤ (0.22314355131420975576629509031 : ℝ) := by
  constructor
  · exact le_log_of (5 / 4 : ℝ) (1 / 9 : ℝ) (13889 / 125000 : ℝ) _ 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])
  · exact log_le_of (5 / 4 : ℝ) (1 / 9 : ℝ) (13889 / 125000 : ℝ) _ 18 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [atanhPS, Finset.sum_range_succ])

lemma log_five_bounds : (1.6094379124341003746007593303 : ℝ) ≤ Real.log (5 : ℝ) ∧ Real.log (5 : ℝ) ≤ (1.6094379124341003746007593504 : ℝ) := by
  obtain ⟨h1, h2⟩ := log_five_quarter_bounds
  obtain ⟨g1, g2⟩ := log_two_bounds
  have e : Real.log (5 : ℝ) = Real.log (5 / 4 : ℝ) + 2 * Real.log (2 : ℝ) := by
    have h : Real.log (5 : ℝ) = Real.log ((5 / 4 : ℝ) * 2 ^ 2) := by
      congr 1
      norm_num
    rw [h, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [e]
  constructor <;> linarith

/-- Final numeric lemma for Bai's bound.  Rates (per `n`), with `δ` the slack of the assembly
(lcm bound, prime saving and constants), `ω` a certified lower bound of the prime saving:
`s` bounds `|V_n|`, `t` bounds `|Λ_n|`, `g` bounds `|Λ_n| / |V_n|`. -/
theorem final_numeric (ω δ s t g : ℝ) (hω : 1202.565773361291 ≤ ω) (hω' : ω ≤ 1203)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1e-16)
    (hs : s = 7430 - 929 * Real.log 2 - ω + Real.log 25 + 15979.97420422751 + 100000 * δ)
    (ht : t = 6542.209753096835 - (7430 - 4645 * Real.log 2 - ω) - 100000 * δ)
    (hg : g = 6542.209753096835 + 3716 * Real.log 2 + Real.log 25 + 15979.974204227497 - 100000 * δ) :
    0 < s ∧ 0 < t ∧ s < g ∧ 1 + s / t ≤ 7.101862832357 ∧ 1 + s / (g - s) ≤ 7.101862832357 := by
  obtain ⟨g1, g2⟩ := log_two_bounds
  obtain ⟨f1, f2⟩ := log_five_bounds
  have e25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [e25] at hs hg
  have hs0 : 0 < s := by rw [hs]; linarith
  have ht0 : 0 < t := by rw [ht]; linarith
  have hgs : s < g := by rw [hs, hg]; linarith
  have hgs0 : 0 < g - s := by linarith
  refine ⟨hs0, ht0, hgs, ?_, ?_⟩
  · have : s / t ≤ 7.101862832357 - 1 := by
      rw [div_le_iff₀ ht0, hs, ht]; linarith
    linarith
  · have : s / (g - s) ≤ 7.101862832357 - 1 := by
      rw [div_le_iff₀ hgs0, hs, hg]; linarith
    linarith

end BaiLogs

theorem solution (ω δ s t g : ℝ) (hω : 1202.565773361291 ≤ ω) (hω' : ω ≤ 1203)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1e-16)
    (hs : s = 7430 - 929 * Real.log 2 - ω + Real.log 25 + 15979.97420422751 + 100000 * δ)
    (ht : t = 6542.209753096835 - (7430 - 4645 * Real.log 2 - ω) - 100000 * δ)
    (hg : g = 6542.209753096835 + 3716 * Real.log 2 + Real.log 25 + 15979.974204227497 - 100000 * δ) :
    0 < s ∧ 0 < t ∧ s < g ∧ 1 + s / t ≤ 7.101862832357 ∧ 1 + s / (g - s) ≤ 7.101862832357 := by
  exact BaiLogs.final_numeric ω δ s t g hω hω' hδ hδ' hs ht hg
