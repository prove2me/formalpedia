-- Prove2me | solution 1 for PiIrrationality.mignotte_parameter_selection
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T07:33:17.043988+00:00
-- url     : https://prove2.me/submissions/6cece3b6-fc5c-48e5-86df-aeab40c9c70a

import Mathlib
import Theorems.Thm_MediumPNT


set_option autoImplicit false

theorem mignotte_rate_of_lower_bound (κ : ℝ) (hk : (1957 / 1000 : ℝ)^4 < κ) :
    5 * (5 + 6 * Real.log 2) < 15 * (3 * Real.log κ - 5) := by
  have hbase : 0 < (1957 / 1000 : ℝ)^4 := by norm_num
  have hl := Real.log_lt_log hbase hk
  rw [Real.log_pow] at hl
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 1957 / 2000)
  have heq : Real.log (1957 / 1000) = Real.log (1957 / 2000) + Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (1957 / 2000 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [heq] at hl
  have htwo := Real.log_two_gt_d9
  norm_num at hlo
  linarith

theorem mignotte_kappa_lower_bound :
    (1957 / 1000 : ℝ)^4 <
      (1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4 := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hb2 : (141421 / 100000 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hb3 : (173205 / 100000 : ℝ) < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hc : Real.cos (Real.pi / 12) =
      Real.sqrt 2 / 2 * (Real.sqrt 3 / 2) + Real.sqrt 2 / 2 * (1 / 2) := by
    have heq : Real.pi / 12 = Real.pi / 4 - Real.pi / 6 := by ring
    rw [heq, Real.cos_sub, Real.cos_pi_div_four, Real.cos_pi_div_six,
      Real.sin_pi_div_four, Real.sin_pi_div_six]
  have hclo : (96592 / 100000 : ℝ) < Real.cos (Real.pi / 12) := by
    rw [hc]
    nlinarith [mul_pos (sub_pos.mpr hb2) (sub_pos.mpr hb3)]
  have hspos : 0 < Real.sin (Real.pi / 24) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have hsne : Real.sin (Real.pi / 24) ≠ 0 := ne_of_gt hspos
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / 24)
  have hdbl := Real.cos_two_mul (Real.pi / 24)
  have heq : 2 * (Real.pi / 24) = Real.pi / 12 := by ring
  rw [heq] at hdbl
  have hk : (1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4 =
      1 / (4 * Real.sin (Real.pi / 24)^2) := by
    field_simp
    nlinarith [htrig]
  rw [hk]
  apply (lt_div_iff₀ (by positivity : 0 < 4 * Real.sin (Real.pi / 24)^2)).2
  nlinarith

theorem mignotte_rate :
    5 * (5 + 6 * Real.log 2) <
      15 * (3 * Real.log ((1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4) - 5) :=
  mignotte_rate_of_lower_bound _ mignotte_kappa_lower_bound


set_option autoImplicit false
open Filter Asymptotics
open scoped Topology

namespace PiIrrationality

theorem eventual_psi_upper (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + δ) * x := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C, hC, hbound⟩ := hO.exists_pos
  have ht : Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
    simpa only [neg_mul, Function.comp_def] using tendsto_neg_atTop_atBot.comp (hh.const_mul_atTop hc)
  have he : ∀ᶠ x : ℝ in atTop,
      C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) < δ :=
    (show Tendsto (fun x : ℝ => C * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) by simpa using ht.const_mul C).eventually_lt_const hδ
  filter_upwards [hbound.bound, he, eventually_ge_atTop (0 : ℝ)] with x hx he hx0
  have hxp := Real.exp_pos (-c * (Real.log x) ^ ((1 : ℝ) / 10))
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg hx0,
    abs_of_nonneg (mul_nonneg hx0 hxp.le)] at hx
  have hab := le_abs_self (Chebyshev.psi x - x)
  nlinarith

theorem eventual_lcm_upper (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N,
      (Nat.lcmUpto n : ℝ) ≤ Real.exp ((1 + δ) * n) := by
  have h := tendsto_natCast_atTop_atTop.eventually (eventual_psi_upper δ hδ)
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  have hlog := hN n hn
  rw [Chebyshev.psi_eq_log_lcmUpto] at hlog
  have hnpos : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  simpa only [Real.exp_log hnpos] using Real.exp_le_exp.mpr hlog

end PiIrrationality


set_option autoImplicit false
open Filter
open scoped Topology

lemma mignotte_polynomial_absorption (C ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ)^3 ≤ Real.exp (ε * n) := by
  have ht : Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hε
  have hz := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).comp ht
  have hz' : Tendsto (fun n : ℕ => C * (n : ℝ)^3 * Real.exp (-(ε * n))) atTop (𝓝 0) := by
    have := hz.const_mul (C / ε^3)
    simpa only [mul_zero] using this.congr (fun n => by
      dsimp
      field_simp
      )
  have he : ∀ᶠ n : ℕ in atTop, C * (n : ℝ)^3 * Real.exp (-(ε * n)) < 1 :=
    hz'.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, fun n hn => ?_⟩
  have hh := (mul_lt_mul_iff_left₀ (Real.exp_pos (ε * n))).2 (hN n hn)
  rw [mul_assoc, ← Real.exp_add] at hh
  simpa using hh.le

lemma mignotte_select_integer (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hrate : 5 * B < 15 * A) (N : ℕ) :
    ∃ Q : ℕ, ∀ q : ℕ, 0 < q → Q ≤ q → ∃ n : ℕ, N ≤ n ∧
      5 * Real.log q ≤ A * n ∧ B * n < 15 * Real.log q := by
  have hr : 5 / A < 15 / B := (div_lt_div_iff₀ hA hB).2 hrate
  obtain ⟨k, hk1, hk2⟩ := exists_between hr
  have hk : 0 < k := lt_trans (div_pos (by norm_num) hA) hk1
  have hAk : 5 < A * k := by nlinarith [(div_lt_iff₀ hA).1 hk1]
  have hBk : B * k < 15 := by nlinarith [(lt_div_iff₀ hB).1 hk2]
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ q : ℕ in atTop,
      max ((N : ℝ) / k) (B / (15 - B*k) + 1) ≤ Real.log q :=
    hlog.eventually (eventually_ge_atTop _)
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 hev
  refine ⟨Q, fun q hq hQq => ?_⟩
  have hbound := hQ q hQq
  have hlogN := le_trans (le_max_left _ _) hbound
  have hlogB := le_trans (le_max_right _ _) hbound
  have hlogpos : 0 < Real.log (q : ℝ) := by
    have : 0 < B / (15 - B*k) := div_pos hB (by linarith)
    linarith
  let n := Nat.ceil (k * Real.log (q : ℝ))
  have hnlo : k * Real.log (q : ℝ) ≤ (n : ℝ) := Nat.le_ceil _
  have hnhi : (n : ℝ) < k * Real.log (q : ℝ) + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (mul_pos hk hlogpos))
  refine ⟨n, ?_, ?_, ?_⟩
  · have : (N : ℝ) ≤ (n : ℝ) := by
      have := (div_le_iff₀ hk).1 hlogN
      nlinarith
    exact_mod_cast this
  · nlinarith [mul_pos (sub_pos.mpr hAk) hlogpos]
  · have hh := (div_le_iff₀ (by linarith : 0 < 15 - B*k)).1 (show B / (15 - B*k) ≤ Real.log (q : ℝ) - 1 by linarith)
    nlinarith

theorem mignotte_parameter_selection_of_lcm_bound
    (hN : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (Nat.lcmUpto n : ℝ) ≤ Real.exp ((1 + δ) * n)) :
    ∃ Q : ℕ, ∀ q : ℕ, 0 < q → Q ≤ q →
      ∃ n : ℕ, 40000 ≤ n ∧
      13 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 * Real.exp (-3 * n * Real.log ((1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4)) ≤ (1 / (32 * (q : ℝ)^5)) / 2 ∧
      25 * (Nat.lcmUpto n : ℝ)^5 * (2 : ℝ)^(6*n) * (n : ℝ)^3 < (q : ℝ)^15 / 32 := by
  let κ := (1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4
  let a := 3 * Real.log κ - 5
  let b := 5 + 6 * Real.log 2
  have hb : 0 < b := by dsimp [b]; linarith [Real.log_two_gt_d9]
  have hr : 5 * b < 15 * a := mignotte_rate
  let ε := (15*a - 5*b) / 40
  have hε : 0 < ε := by dsimp [ε]; linarith
  let A := a - ε
  let B := b + ε
  have hB : 0 < B := by dsimp [B]; linarith
  have hrate : 5 * B < 15 * A := by dsimp [A, B, ε]; linarith
  have hA : 0 < A := by nlinarith
  obtain ⟨N₁, hN₁⟩ := hN (ε / 10) (by positivity)
  obtain ⟨N₂, hN₂⟩ := mignotte_polynomial_absorption 832 (ε / 2) (by positivity)
  obtain ⟨Q, hQ⟩ := mignotte_select_integer A B hA hB hrate (max 40000 (max N₁ N₂))
  refine ⟨Q, fun q hq hQq => ?_⟩
  obtain ⟨n, hn, hnA, hnB⟩ := hQ q hq hQq
  have hn40000 : 40000 ≤ n := le_trans (le_max_left _ _) hn
  have hnN : max N₁ N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hpoly := hN₂ n (le_trans (le_max_right _ _) hnN)
  have hlcm := hN₁ n (le_trans (le_max_left _ _) hnN)
  have hlcm5 : (Nat.lcmUpto n : ℝ)^5 ≤ Real.exp (5 * ((1 + ε / 10) * n)) := by
    have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Nat.lcmUpto n) hlcm 5
    have he := Real.exp_nat_mul ((1 + ε / 10) * (n : ℝ)) 5
    norm_num at he
    rw [he]
    exact this
  have hcombined : 832 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 ≤
      Real.exp ((5 + ε) * n) := by
    calc
      _ ≤ Real.exp (ε / 2 * n) * Real.exp (5 * ((1 + ε / 10) * n)) :=
        mul_le_mul hpoly hlcm5 (by positivity) (le_of_lt (Real.exp_pos _))
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hR : 64 * (13 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 * Real.exp (-3 * n * Real.log κ)) ≤
      Real.exp (-A * n) := by
    calc
      _ = (832 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5) * Real.exp (-3 * n * Real.log κ) := by ring
      _ ≤ Real.exp ((5 + ε) * n) * Real.exp (-3 * n * Real.log κ) :=
        mul_le_mul_of_nonneg_right hcombined (le_of_lt (Real.exp_pos _))
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A, a]; ring
  have hpow : (2 : ℝ)^(6*n) = Real.exp (6 * n * Real.log 2) := by
    have he : 6 * (n : ℝ) * Real.log 2 = ((6*n : ℕ) : ℝ) * Real.log 2 := by push_cast; ring
    rw [he, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hT : 32 * (25 * (Nat.lcmUpto n : ℝ)^5 * (2 : ℝ)^(6*n) * (n : ℝ)^3) ≤
      Real.exp (B * n) := by
    calc
      _ ≤ (832 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5) * (2 : ℝ)^(6*n) := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5) (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(6*n))]
      _ ≤ Real.exp ((5 + ε) * n) * (2 : ℝ)^(6*n) :=
        mul_le_mul_of_nonneg_right hcombined (by positivity)
      _ = _ := by rw [hpow, ← Real.exp_add]; congr 1; dsimp [B, b]; ring
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hRexp : Real.exp (-A * n) ≤ 1 / (q : ℝ)^5 := by
    calc
      _ ≤ Real.exp (-(5 * Real.log (q : ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by
        have he := Real.exp_nat_mul (Real.log (q : ℝ)) 5
        norm_num at he
        rw [Real.exp_neg, he, Real.exp_log hqpos, one_div]
  have hTexp : Real.exp (B * n) < (q : ℝ)^15 := by
    calc
      _ < Real.exp (15 * Real.log (q : ℝ)) := Real.exp_lt_exp.mpr hnB
      _ = _ := by
        have he := Real.exp_nat_mul (Real.log (q : ℝ)) 15
        norm_num at he
        rw [he, Real.exp_log hqpos]
  refine ⟨n, hn40000, ?_, ?_⟩
  · change 13 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 * Real.exp (-3 * n * Real.log κ) ≤ _
    have hh := le_trans hR hRexp
    have heq : (1 / (32 * (q : ℝ)^5)) / 2 = (1 / (q : ℝ)^5) / 64 := by ring
    rw [heq]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 64)).2
    nlinarith
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 32)).2
    nlinarith [lt_of_le_of_lt hT hTexp]

theorem solution :
    ∃ Q : ℕ, ∀ q : ℕ, 0 < q → Q ≤ q →
      ∃ n : ℕ, 40000 ≤ n ∧
      13 * (n : ℝ)^3 * (Nat.lcmUpto n : ℝ)^5 * Real.exp (-3 * n * Real.log ((1 + (Real.cos (Real.pi / 24) / Real.sin (Real.pi / 24))^2) / 4)) ≤ (1 / (32 * (q : ℝ)^5)) / 2 ∧
      25 * (Nat.lcmUpto n : ℝ)^5 * (2 : ℝ)^(6*n) * (n : ℝ)^3 < (q : ℝ)^15 / 32 :=
  mignotte_parameter_selection_of_lcm_bound PiIrrationality.eventual_lcm_upper
