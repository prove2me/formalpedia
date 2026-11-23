-- Prove2me | solution 1 for UpperTheory.T3.normPrimesN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:19.714033+00:00
-- url     : https://prove2.me/submissions/8d1d6186-8596-4bdc-a50a-81a0f42ecda6

import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_ShortNorm
import Definitions.Def_Development_AutomorphicArithmetic_ShortNorms_normPrimesN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.Mem.An Filter Topology
namespace UpperTheory.T3
private lemma core_sqrt (A c c' t B Y : ℝ) (hA : 0 < A) (hc : 0 < c)
    (ht : 10000 ≤ t) (htA : 50 * A ≤ t) (htc : 13 / c ^ 2 ≤ t)
    (h2 : 40 * Real.exp (-(1 / 20) * t) ≤ c') (hB : 1 < B) (hBt : Real.log B ≤ 10 * t ^ 2)
    (hY : 0 < Y) (hYt : 8 * t ^ 5 ≤ Real.log Y) :
    1 ≤ Y ∧ Real.log B ≤ c * Real.sqrt (Real.log Y) ∧
      Y ^ ((9 : ℝ) / 10) ≤ c' * 1 * Y / (B ^ A * Real.log Y) := by
  have ht0 : 0 < t := by linarith
  have ht5 : 0 < t ^ 5 := pow_pos ht0 5
  have ht4 : 0 < t ^ 4 := pow_pos ht0 4
  have hL : 0 < Real.log Y := by linarith
  have hY1 : 1 < Y := by
    by_contra h
    push_neg at h
    have := Real.log_nonpos hY.le h
    linarith
  have ht1 : 1 ≤ t := by linarith
  have ht13 : t ≤ t ^ 3 := by
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ 3 := pow_le_pow_right₀ ht1 (by norm_num)
  have ht35 : t ^ 3 ≤ t ^ 5 := pow_le_pow_right₀ ht1 (by norm_num)
  refine ⟨hY1.le, ?_, ?_⟩
  · have hS := Real.sq_sqrt hL.le
    have hS0 := Real.sqrt_nonneg (Real.log Y)
    have hc2 : 0 < c ^ 2 := pow_pos hc 2
    have hct : 13 ≤ c ^ 2 * t := by
      rw [div_le_iff₀ hc2] at htc
      linarith
    have hb : 10 * t ^ 2 ≤ c * Real.sqrt (Real.log Y) := by
      by_contra h
      push_neg at h
      have h1 := mul_self_lt_mul_self (mul_nonneg hc.le hS0) h
      have h2' : c * Real.sqrt (Real.log Y) * (c * Real.sqrt (Real.log Y)) = c ^ 2 * Real.log Y := by
        calc c * Real.sqrt (Real.log Y) * (c * Real.sqrt (Real.log Y))
            = c ^ 2 * (Real.sqrt (Real.log Y) ^ 2) := by ring
          _ = c ^ 2 * Real.log Y := by rw [hS]
      have h3 : c ^ 2 * (8 * t ^ 5) ≤ c ^ 2 * Real.log Y := mul_le_mul_of_nonneg_left hYt hc2.le
      have h4 : t ^ 4 * 13 ≤ t ^ 4 * (c ^ 2 * t) := mul_le_mul_of_nonneg_left hct ht4.le
      nlinarith
    linarith
  · have hB0 : 0 < B := by linarith
    have hc'0 : 0 < c' := lt_of_lt_of_le (by positivity) h2
    have hlogc' : -(1 / 20) * t ≤ Real.log c' := by
      have h := Real.log_le_log (by positivity) h2
      rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
      have : 0 < Real.log 40 := Real.log_pos (by norm_num)
      linarith
    have hlogL : Real.log (Real.log Y) ≤ 38 + Real.log Y / 40 := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hL (show (0:ℝ) < 40 by norm_num))
      rw [Real.log_div hL.ne' (by norm_num)] at h1
      have h2' := Real.log_le_sub_one_of_pos (show (0:ℝ) < 40 by norm_num)
      linarith
    have hAB : A * Real.log B ≤ t ^ 3 / 5 := by
      have a1 : A * Real.log B ≤ A * (10 * t ^ 2) := mul_le_mul_of_nonneg_left hBt hA.le
      have a2 : A * (10 * t ^ 2) ≤ (t / 50) * (10 * t ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have a3 : (t / 50) * (10 * t ^ 2) = t ^ 3 / 5 := by ring
      linarith
    have hexpo : A * Real.log B + Real.log (Real.log Y) ≤ Real.log c' + Real.log Y / 10 := by
      linarith
    have lhs : B ^ A * Real.log Y = Real.exp (A * Real.log B + Real.log (Real.log Y)) := by
      rw [Real.exp_add, Real.exp_log hL, Real.rpow_def_of_pos hB0, mul_comm (Real.log B) A]
    have rhs : c' * Y ^ ((1:ℝ) / 10) = Real.exp (Real.log c' + Real.log Y / 10) := by
      rw [Real.exp_add, Real.exp_log hc'0, Real.rpow_def_of_pos hY]
      congr 2
      ring
    have hmain : B ^ A * Real.log Y ≤ c' * Y ^ ((1:ℝ) / 10) := by
      rw [lhs, rhs]
      exact Real.exp_le_exp.mpr hexpo
    have hden : 0 < B ^ A * Real.log Y := mul_pos (Real.rpow_pos_of_pos hB0 A) hL
    rw [le_div_iff₀ hden]
    calc Y ^ ((9:ℝ) / 10) * (B ^ A * Real.log Y) ≤ Y ^ ((9:ℝ) / 10) * (c' * Y ^ ((1:ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hY _).le
      _ = c' * 1 * (Y ^ ((9:ℝ) / 10) * Y ^ ((1:ℝ) / 10)) := by ring
      _ = c' * 1 * Y := by
          rw [← Real.rpow_add hY]
          norm_num
private lemma eventually_exp_decay_le (c' : ℝ) (hc' : 0 < c') :
    ∀ᶠ t : ℝ in atTop, 40 * Real.exp (-(1 / 20) * t) ≤ c' := by
  filter_upwards [eventually_ge_atTop (-20 * Real.log (c' / 40))] with t ht
  have h1 : -(1 / 20) * t ≤ Real.log (c' / 40) := by linarith
  have h2 := Real.exp_le_exp.mpr h1
  rw [Real.exp_log (div_pos hc' (by norm_num))] at h2
  linarith
private lemma ev_log_sq (eps : ℝ) (he : 0 < eps) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ 2 ≤ x ^ (eps / 5) := by
  have h1 := (isLittleO_log_rpow_atTop (show 0 < eps / 10 by linarith)).bound one_pos
  filter_upwards [h1, eventually_ge_atTop (1:ℝ)] with x hx hx1
  have hxpos : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hp : 0 < x ^ (eps / 10) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_pos hp, one_mul] at hx
  have e : x ^ (eps / 5) = x ^ (eps / 10) * x ^ (eps / 10) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  rw [e, sq]
  exact mul_le_mul hx hx hl hp.le
end UpperTheory.T3
end

set_option autoImplicit false
open GlobalTheory.Mem.An Filter Topology
open UpperTheory UpperTheory.T3
set_option maxHeartbeats 800000
namespace UpperTheory.T3
theorem _root_.solution :
    ShortNorm → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ N d : ℕ, ModAt x eps N d → ∀ Y : ℝ, 0 < Y → 8 * x ^ eps ≤ Real.log Y →
      Y ^ ((9 : ℝ) / 10) ≤ ((normPrimes d N Y (2 * Y)).card : ℝ) := by
  intro hSN eps he
  unfold ShortNorm at hSN
  obtain ⟨A, c, c', hA, hc, hc', hmain⟩ := hSN
  have ht : ∀ᶠ t : ℝ in atTop, 10000 ≤ t ∧ 50 * A ≤ t ∧ 13 / c ^ 2 ≤ t ∧ 40 * Real.exp (-(1 / 20) * t) ≤ c' :=
    (eventually_ge_atTop 10000).and ((eventually_ge_atTop (50 * A)).and
      ((eventually_ge_atTop (13 / c ^ 2)).and (eventually_exp_decay_le c' hc')))
  have hx := (tendsto_rpow_atTop (show 0 < eps / 5 by linarith)).eventually ht
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp (hx.and ((ev_log_sq eps he).and (eventually_ge_atTop (1:ℝ))))
  refine ⟨x₀, fun x hxx N d hMod Y hY hlogY => ?_⟩
  obtain ⟨⟨t1, t2, t3, t4⟩, hls, hx1⟩ := hx₀ x hxx
  unfold ModAt at hMod
  obtain ⟨hdp, hd4, hd100, hN0, hdN, hlogN⟩ := hMod
  have hxpos : 0 < x := by linarith
  have ht5 : (x ^ (eps / 5)) ^ 5 = x ^ eps := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    push_cast
    ring
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hN0' : (0:ℝ) < N := by exact_mod_cast hN0
  have hdN' := Nat.le_of_dvd hN0 hdN
  have hdleN : (d:ℝ) ≤ N := by exact_mod_cast hdN'
  have hlogd : Real.log d ≤ Real.log N := Real.log_le_log hd0 hdleN
  have hN3 : 3 ≤ N := by omega
  have hd100' : (100:ℝ) ≤ d := by exact_mod_cast hd100
  have hB1 : 1 < 4 * (d:ℝ) * (N:ℝ) ^ 2 := by nlinarith
  have hlogB : Real.log (4 * (d:ℝ) * (N:ℝ) ^ 2) = Real.log 4 + Real.log d + 2 * Real.log N := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) hd0.ne') (pow_ne_zero _ hN0'.ne'),
      Real.log_mul (by norm_num) hd0.ne', Real.log_pow]
    push_cast
    ring
  have hBt : Real.log (4 * (d:ℝ) * (N:ℝ) ^ 2) ≤ 10 * (x ^ (eps / 5)) ^ 2 := by
    rw [hlogB]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
    have q := mul_le_mul_of_nonneg_left hls (show 0 ≤ 3 * x ^ (eps / 5) by linarith)
    have big : 10000 * 10000 ≤ x ^ (eps / 5) * x ^ (eps / 5) := mul_le_mul t1 t1 (by norm_num) (by linarith)
    nlinarith
  have hYt : 8 * (x ^ (eps / 5)) ^ 5 ≤ Real.log Y := by rw [ht5]; exact hlogY
  obtain ⟨hY1, hsq, hfin⟩ := core_sqrt A c c' (x ^ (eps / 5)) (4 * (d:ℝ) * (N:ℝ) ^ 2) Y hA hc t1 t2 t3 t4 hB1 hBt hY hYt
  have hexp : Real.exp (-c * Real.sqrt (Real.log Y)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := Real.sqrt_nonneg (Real.log Y)
    nlinarith
  have key := hmain d N Y 1 hdp hd4 hd100 hN3 hY1 hsq hexp le_rfl
  have e : Y * (1 + 1) = 2 * Y := by ring
  rw [e] at key
  exact le_trans hfin key
end UpperTheory.T3
