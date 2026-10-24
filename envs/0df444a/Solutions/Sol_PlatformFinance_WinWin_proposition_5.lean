-- Prove2me | solution 1 for PlatformFinance.WinWin.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T00:24:18.478464+00:00
-- url     : https://prove2.me/submissions/005715e1-3e5a-4333-801f-44091c3c08cd

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model
import Theorems.Thm_PlatformFinance_WinWin_profits_T
import Theorems.Thm_PlatformFinance_WinWin_profits_P

/-!
Proposition 5 of Huang, Lai, Wang & Xiao (SSRN 4014045, p. 18): reduction to the closed-form
equilibrium profits `PlatformFinance.WinWin.profits_T` (trade credit) and
`PlatformFinance.WinWin.profits_P` (platform financing). The comparison with the threshold
r̂₂ is proved here in full: the platform supplier profit, as a function of `R = c(1+r)`, is
the continuous strictly decreasing function `PFW5.G`, and it meets the trade-credit profit
exactly at `R = c(1 + r̂₂)` (r₃ and r₄ are the smaller roots of the matching equations).
-/

set_option autoImplicit false

namespace PFW5
open PlatformFinance.WinWin

lemma sqrt6_gt : (2.449:ℝ) < Real.sqrt 6 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num
lemma sqrt6_lt : Real.sqrt 6 < 2.4495 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num
lemma sqrt10_gt : (3.1622:ℝ) < Real.sqrt 10 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num
lemma sqrt10_lt : Real.sqrt 10 < 3.1623 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma le_of_sq_le' {z y : ℝ} (hy : 0 ≤ y) (h : z ^ 2 ≤ y ^ 2) : z ≤ y := by
  by_contra hc; have hc' := not_le.mp hc; nlinarith

/-- Generic comparison with the smaller root `r₃`. -/
lemma r3_ge (a δ k c u R L N D T : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hk : 0 < k) (hc : 0 < c)
    (hu : 0 < u) (hK : 0 ≤ a * k - c * u) (hRA : R ≤ (a + δ) * k)
    (hh : 0 ≤ 2 * (c * u) * ((a + δ) * k - R) ^ 2 - 3 * R * (a * k - c * u) ^ 2)
    (hL : L = R / c - 1)
    (hT : T = 3 * a ^ 2 * k ^ 2 + 3 * c ^ 2 * u ^ 2 + (2 * a * c + 8 * c * δ) * u * k)
    (hN : N = 3 * a ^ 2 * k ^ 2 + 3 * c ^ 2 * u ^ 2 - 2 * c * (a - 2 * δ) * u * k - 4 * c ^ 2 * u
      - Real.sqrt 3 * (a * k - c * u) * Real.sqrt T)
    (hD : D = 4 * c ^ 2 * u) : L ≤ N / D := by
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hDpos : 0 < D := by rw [hD]; positivity
  rw [hL, le_div_iff₀ hDpos]
  have e : (R / c - 1) * D = 4 * c * u * R - 4 * c ^ 2 * u := by
    rw [hD]; field_simp
  rw [e, hN]
  set y := 3 * a ^ 2 * k ^ 2 + 3 * c ^ 2 * u ^ 2 - 2 * c * (a - 2 * δ) * u * k - 4 * c * u * R
    with hy
  have hz2 : (Real.sqrt 3 * (a * k - c * u) * Real.sqrt T) ^ 2
      = 3 * (a * k - c * u) ^ 2 * T := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hT0]
  have hy0 : 0 ≤ y := by
    have : y = 4 * (c * u) * ((a + δ) * k - R) + 3 * (a * k - c * u) ^ 2 := by
      rw [hy]; ring
    rw [this]
    have : 0 ≤ (a + δ) * k - R := by linarith
    positivity
  have hid : y ^ 2 - 3 * (a * k - c * u) ^ 2 * T
      = 8 * (c * u) * (2 * (c * u) * ((a + δ) * k - R) ^ 2 - 3 * R * (a * k - c * u) ^ 2) := by
    rw [hy, hT]; ring
  have hcu : 0 < c * u := by positivity
  have : Real.sqrt 3 * (a * k - c * u) * Real.sqrt T ≤ y := by
    apply le_of_sq_le' hy0
    rw [hz2]; nlinarith [mul_nonneg hcu.le hh]
  linarith

/-- Generic comparison with the smaller root `r₄`. -/
lemma r4_ge (c u A m R L N D T : ℝ) (hc : 0 < c) (hu : 0 < u) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hRA : R ≤ A) (hh : 0 ≤ 9 * (c * u) * (A - R) ^ 2 - 4 * m * R)
    (hL : L = R / c - 1) (hT : T = m ^ 2 + 9 * (c * u) * A * m)
    (hN : N = 9 * c * u * (A - c) + 2 * m - 2 * Real.sqrt T)
    (hD : D = 9 * c ^ 2 * u) : L ≤ N / D := by
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hDpos : 0 < D := by rw [hD]; positivity
  rw [hL, le_div_iff₀ hDpos]
  have e : (R / c - 1) * D = 9 * c * u * R - 9 * c ^ 2 * u := by
    rw [hD]; field_simp
  rw [e, hN]
  have hcu : 0 < c * u := by positivity
  have hy0 : 0 ≤ 9 * (c * u) * (A - R) + 2 * m := by
    have : 0 ≤ A - R := by linarith
    positivity
  have : 2 * Real.sqrt T ≤ 9 * (c * u) * (A - R) + 2 * m := by
    apply le_of_sq_le' hy0
    rw [mul_pow, Real.sq_sqrt hT0, hT]
    nlinarith [mul_nonneg hcu.le hh]
  nlinarith

/-- Facts about `S` and `K`. -/
lemma S_facts (a δ φ c rf : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hK : 0 < K0 a φ c rf) :
    δ * (1 - φ) * Sroot a δ φ c rf ^ 2 = (δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf) ∧
      1 < Sroot a δ φ c rf ∧
      Kfun a δ φ c rf = δ * (1 - φ) * (Sroot a δ φ c rf - 1) ^ 2 * (2 * Sroot a δ φ c rf + 1) := by
  unfold K0 at hK
  have hk : 0 < 1 - φ := by linarith
  have hdk : 0 < δ * (1 - φ) := by positivity
  set X := (δ + 3 * a) * (1 - φ) - 3 * c * (1 + rf) with hXdef
  have hX : δ * (1 - φ) < X := by rw [hXdef]; nlinarith
  have hq : 1 < X / (δ * (1 - φ)) := by rw [lt_div_iff₀ hdk]; linarith
  have hS2 : Sroot a δ φ c rf ^ 2 = X / (δ * (1 - φ)) := by
    unfold Sroot; rw [Real.sq_sqrt (by linarith)]
  have h1 : δ * (1 - φ) * Sroot a δ φ c rf ^ 2 = X := by
    rw [hS2]; field_simp
  refine ⟨h1, ?_, ?_⟩
  · unfold Sroot; rw [Real.lt_sqrt (by norm_num)]; linarith
  · have hS0 : 0 ≤ Sroot a δ φ c rf := Real.sqrt_nonneg _
    set S := Sroot a δ φ c rf with hSdef
    have e3 : X ^ 3 / (δ * (1 - φ)) = (δ * (1 - φ) * S ^ 3) ^ 2 := by
      rw [← h1]; field_simp
    unfold Kfun
    rw [← hXdef, e3, Real.sqrt_sq (by positivity)]
    linear_combination 3 * h1

lemma delta13 (a φ c rf : ℝ) (hφ1 : φ < 1) (hK : 0 < K0 a φ c rf) :
    delta1 a φ c rf < delta3 a φ c rf := by
  have hk : 0 < 1 - φ := by linarith
  have s6b := sqrt6_lt
  have s10b := sqrt10_lt
  unfold delta1 delta3
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hneg : 215 * Real.sqrt 10 + 320 * Real.sqrt 6 - 1466 < 0 := by linarith
  have := mul_lt_mul_of_pos_left hneg (mul_pos hK hk)
  linear_combination this

lemma Sbound (a δ φ c rf : ℝ) (hδ : 0 < δ) (hφ1 : φ < 1) (hK : 0 < K0 a φ c rf)
    (h : delta1 a φ c rf < δ) : Sroot a δ φ c rf < 3.777 := by
  have hk : 0 < 1 - φ := by linarith
  have hdk : 0 < δ * (1 - φ) := by positivity
  have s10a := sqrt10_gt
  obtain ⟨hS1, hS, -⟩ := S_facts a δ φ c rf hδ hφ1 hK
  set S := Sroot a δ φ c rf with hSdef
  unfold delta1 at h
  rw [div_lt_iff₀ (by positivity)] at h
  have h3K : 3 * K0 a φ c rf = δ * (1 - φ) * (S ^ 2 - 1) := by
    unfold K0; linear_combination -hS1
  have hS2 : 0 < S ^ 2 - 1 := by nlinarith
  have h' : (5 * Real.sqrt 10 - 14) * (S ^ 2 - 1) * (δ * (1 - φ)) < 24 * (δ * (1 - φ)) := by
    have : (5 * Real.sqrt 10 - 14) * (S ^ 2 - 1) * (δ * (1 - φ))
        = 3 * ((5 * Real.sqrt 10 - 14) * K0 a φ c rf) := by
      linear_combination (-(5 * Real.sqrt 10 - 14)) * h3K
    rw [this]; linarith
  have h'' := lt_of_mul_lt_mul_right h' hdk.le
  have : S ^ 2 < 14.2525 := by nlinarith
  nlinarith

lemma caseB_hh (k δ C K R A s : ℝ) (hC : 0 < C) (hK : 0 < K) (hKd : K < (s + 2) * k * δ)
    (hRC : R ≤ C) (hs2 : s ^ 2 = 6) (hAR : (A - R) ^ 2 = (15 + 6 * s) * k ^ 2 * δ ^ 2) :
    0 ≤ 2 * C * (A - R) ^ 2 - 3 * R * K ^ 2 := by
  rw [hAR]
  have e2 : K ^ 2 < ((s + 2) * k * δ) ^ 2 := pow_lt_pow_left₀ hKd hK.le two_ne_zero
  have h1 := mul_lt_mul_of_pos_left e2 hC
  have h2 := mul_le_mul_of_nonneg_left hRC (sq_nonneg K)
  have e3 : ((s + 2) * k * δ) ^ 2 = (10 + 4 * s) * k ^ 2 * δ ^ 2 := by
    linear_combination (k ^ 2 * δ ^ 2) * hs2
  rw [e3] at h1
  nlinarith

lemma caseC_hh (k δ C R A S s : ℝ) (hk : 0 < k) (hδ : 0 < δ) (hC : 0 < C) (hRC : R ≤ C)
    (hS : 1 < S) (hSb : S < 3.777) (hs : 2.449 < s)
    (hAR : (A - R) ^ 2 = (15 + 6 * s) * k ^ 2 * δ ^ 2) :
    0 ≤ 9 * C * (A - R) ^ 2 - 4 * (δ * k * (δ * k * (S - 1) ^ 2 * (2 * S + 1))) * R := by
  have hkap0 : 0 ≤ (S - 1) ^ 2 * (2 * S + 1) := by positivity
  have hkap : 4 * ((S - 1) ^ 2 * (2 * S + 1)) ≤ 9 * (15 + 6 * s) := by
    have e1 : (S - 1) ^ 2 ≤ 2.777 ^ 2 := by nlinarith
    have e2 : 2 * S + 1 ≤ 8.554 := by linarith
    have := mul_le_mul e1 e2 (by linarith) (by norm_num)
    nlinarith
  have hb : 0 ≤ 9 * C * (15 + 6 * s) - 4 * ((S - 1) ^ 2 * (2 * S + 1)) * R := by
    have h1 := mul_le_mul_of_nonneg_right hkap hC.le
    have h2 := mul_le_mul_of_nonneg_left hRC hkap0
    linarith
  rw [hAR]
  have : 9 * C * ((15 + 6 * s) * k ^ 2 * δ ^ 2)
      - 4 * (δ * k * (δ * k * (S - 1) ^ 2 * (2 * S + 1))) * R
      = (δ * k) ^ 2 * (9 * C * (15 + 6 * s) - 4 * ((S - 1) ^ 2 * (2 * S + 1)) * R) := by ring
  rw [this]; positivity

lemma delta21 (a φ c rf : ℝ) (hφ1 : φ < 1) (hK : 0 < K0 a φ c rf) :
    delta2 a φ c rf < delta1 a φ c rf := by
  have hk : 0 < 1 - φ := by linarith
  have s6a := sqrt6_gt
  have s10a := sqrt10_gt
  have h6 : 0 < Real.sqrt 6 + 2 := by linarith
  unfold delta1 delta2
  rw [div_lt_div_iff₀ (mul_pos h6 hk) (by positivity)]
  have hprod : 8 < (5 * Real.sqrt 10 - 14) * (Real.sqrt 6 + 2) := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 5 * Real.sqrt 10 - 14 - 1.811)
      (by linarith : (0:ℝ) < Real.sqrt 6 + 2 - 4.449)]
  have := mul_lt_mul_of_pos_left hprod (mul_pos hK hk)
  linear_combination this

lemma dec_le (C D L R R' : ℝ) (hC : 0 < C) (hD : 0 < D) (hR : 0 < R) (hRR : R ≤ R')
    (hRL : R' ≤ L) : C * (L - R') ^ 2 / (D * R') ≤ C * (L - R) ^ 2 / (D * R) := by
  have hR' : 0 < R' := by linarith
  rw [div_le_div_iff₀ (mul_pos hD hR') (mul_pos hD hR)]
  have h1 : R * R' ≤ L * L := mul_le_mul (by linarith) hRL hR'.le (by linarith)
  have hid : C * (L - R) ^ 2 * (D * R') - C * (L - R') ^ 2 * (D * R)
      = C * D * ((R' - R) * (L * L - R * R')) := by ring
  have : 0 ≤ C * (L - R) ^ 2 * (D * R') - C * (L - R') ^ 2 * (D * R) := by
    rw [hid]
    exact mul_nonneg (mul_nonneg hC.le hD.le) (mul_nonneg (by linarith) (by linarith))
  linarith

lemma dec_lt (C D L R R' : ℝ) (hC : 0 < C) (hD : 0 < D) (hR : 0 < R) (hRR : R < R')
    (hRL : R' ≤ L) : C * (L - R') ^ 2 / (D * R') < C * (L - R) ^ 2 / (D * R) := by
  have hR' : 0 < R' := by linarith
  rw [div_lt_div_iff₀ (mul_pos hD hR') (mul_pos hD hR)]
  have h1 : R * R' < R' * R' := mul_lt_mul_of_pos_right hRR hR'
  have h2 : R' * R' ≤ L * L := mul_self_le_mul_self hR'.le hRL
  have hid : C * (L - R) ^ 2 * (D * R') - C * (L - R') ^ 2 * (D * R)
      = C * D * ((R' - R) * (L * L - R * R')) := by ring
  have : 0 < C * (L - R) ^ 2 * (D * R') - C * (L - R') ^ 2 * (D * R) := by
    rw [hid]
    exact mul_pos (mul_pos hC hD) (mul_pos (by linarith) (by linarith))
  linarith

/-- The platform-financing supplier profit as a function of `R = c(1+r)`. -/
noncomputable def G (k C M A R0 R : ℝ) : ℝ :=
  if R ≤ R0 then C * (M - R) ^ 2 / (8 * k * R) else C * (A - R) ^ 2 / (12 * k * R)

lemma G_bd (k C M A R0 : ℝ) (hk : 0 < k) (hR0 : 0 < R0)
    (hbd : 12 * (M - R0) ^ 2 = 8 * (A - R0) ^ 2) :
    C * (M - R0) ^ 2 / (8 * k * R0) = C * (A - R0) ^ 2 / (12 * k * R0) := by
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (C * k * R0) * hbd

lemma G_anti (k C M A R0 R R' : ℝ) (hk : 0 < k) (hC : 0 < C) (hR0M : R0 < M)
    (hbd : 12 * (M - R0) ^ 2 = 8 * (A - R0) ^ 2) (hR : 0 < R) (hRR : R ≤ R')
    (hRA : R' ≤ A) :
    G k C M A R0 R' ≤ G k C M A R0 R ∧ (R < R' → G k C M A R0 R' < G k C M A R0 R) := by
  have h8 : (0:ℝ) < 8 * k := by positivity
  have h12 : (0:ℝ) < 12 * k := by positivity
  unfold G
  by_cases h' : R' ≤ R0
  · have h : R ≤ R0 := le_trans hRR h'
    rw [if_pos h, if_pos h']
    exact ⟨dec_le C (8 * k) M R R' hC h8 hR hRR (by linarith),
      fun hl => dec_lt C (8 * k) M R R' hC h8 hR hl (by linarith)⟩
  · rw [if_neg h']
    by_cases h : R ≤ R0
    · rw [if_pos h]
      have hR0 : 0 < R0 := lt_of_lt_of_le hR h
      have heq := G_bd k C M A R0 hk hR0 hbd
      have h1 := dec_le C (8 * k) M R R0 hC h8 hR h hR0M.le
      have h2 := dec_lt C (12 * k) A R0 R' hC h12 hR0 (not_le.mp h') hRA
      exact ⟨by linarith, fun _ => by linarith⟩
    · rw [if_neg h]
      exact ⟨dec_le C (12 * k) A R R' hC h12 hR hRR hRA,
        fun hl => dec_lt C (12 * k) A R R' hC h12 hR hl hRA⟩

lemma G_branch2 (k C M A R0 R : ℝ) (hk : 0 < k) (hR : 0 < R) (hle : R0 ≤ R)
    (hbd : 12 * (M - R0) ^ 2 = 8 * (A - R0) ^ 2) :
    G k C M A R0 R = C * (A - R) ^ 2 / (12 * k * R) := by
  unfold G
  by_cases h : R ≤ R0
  · rw [if_pos h]
    have he : R = R0 := le_antisymm h hle
    subst he
    exact G_bd k C M A R hk hR hbd
  · rw [if_neg h]

lemma r3_root (C A K Rh z T : ℝ) (hT : T = 8 * C * A + 3 * K ^ 2) (hz : z ^ 2 = 3 * K ^ 2 * T)
    (hR : 4 * C * Rh = 4 * C * A + 3 * K ^ 2 - z) :
    8 * C * (2 * C * (A - Rh) ^ 2 - 3 * Rh * K ^ 2) = 0 := by
  linear_combination (4 * C * Rh + (4 * C * A + 3 * K ^ 2 - z) - 8 * C * A - 6 * K ^ 2) * hR
    + hz + 3 * K ^ 2 * hT

lemma r4_root (C A m Rh s T : ℝ) (hT : T = m ^ 2 + 9 * C * A * m) (hs : s ^ 2 = T)
    (hR : 9 * C * Rh = 9 * C * A + 2 * m - 2 * s) :
    9 * C * (9 * C * (A - Rh) ^ 2 - 4 * m * Rh) = 0 := by
  linear_combination (9 * C * Rh + (9 * C * A + 2 * m - 2 * s) - 18 * C * A - 4 * m) * hR
    + 4 * hs + 4 * hT

lemma PiP (a δ φ c rf r : ℝ) (hφ1 : φ < 1) (hc : 0 < c) (hr : -1 < r) (X : ℝ)
    (hX : X = if δ ≤ deltaR a φ c r then
          (1 + rf) * (a * (1 - φ) - c * (1 + r)) ^ 2 / (8 * (r + 1) * (1 - φ))
         else (1 + rf) * ((a + δ) * (1 - φ) - c * (1 + r)) ^ 2 / (12 * (1 + r) * (1 - φ))) :
    X = G (1 - φ) (c * (1 + rf)) (a * (1 - φ)) ((a + δ) * (1 - φ))
      ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) (c * (1 + r)) := by
  have hk : 0 < 1 - φ := by linarith
  have hr1 : 0 < 1 + r := by linarith
  have hr1' : 0 < r + 1 := by linarith
  have hcr : 0 < c * (1 + r) := mul_pos hc hr1
  have hs : 0 < 2 + Real.sqrt 6 := by positivity
  have hiff : δ ≤ deltaR a φ c r ↔ c * (1 + r) ≤ (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) := by
    unfold deltaR
    rw [le_div_iff₀ (mul_pos hs hk)]
    constructor <;> intro h <;> linarith
  have e1 : 8 * (r + 1) * (1 - φ) ≠ 0 := (mul_pos (mul_pos (by norm_num) hr1') hk).ne'
  have e2 : 12 * (1 + r) * (1 - φ) ≠ 0 := (mul_pos (mul_pos (by norm_num) hr1) hk).ne'
  have e3 : 8 * (1 - φ) * (c * (1 + r)) ≠ 0 := (mul_pos (mul_pos (by norm_num) hk) hcr).ne'
  have e4 : 12 * (1 - φ) * (c * (1 + r)) ≠ 0 := (mul_pos (mul_pos (by norm_num) hk) hcr).ne'
  rw [hX]; unfold G
  by_cases h : δ ≤ deltaR a φ c r
  · rw [if_pos h, if_pos (hiff.1 h), div_eq_div_iff e1 e3]; ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h')), div_eq_div_iff e2 e4]; ring

lemma r3_case (C A K Rh z T : ℝ) (hC : 0 < C) (hA : 0 < A) (hz0 : 0 ≤ z)
    (hT : T = 8 * C * A + 3 * K ^ 2) (hz : z ^ 2 = 3 * K ^ 2 * T)
    (hR : 4 * C * Rh = 4 * C * A + 3 * K ^ 2 - z) :
    0 < Rh ∧ Rh ≤ A ∧ 2 * C * (A - Rh) ^ 2 - 3 * Rh * K ^ 2 = 0 := by
  have hCA : 0 < C * A := mul_pos hC hA
  have hz' : z ^ 2 = 24 * (C * A) * K ^ 2 + 9 * (K ^ 2) ^ 2 := by rw [hz, hT]; ring
  refine ⟨?_, ?_, ?_⟩
  · have hlt : z < 4 * (C * A) + 3 * K ^ 2 := by
      by_contra hcon
      have hge := not_lt.mp hcon
      have h0 : 0 ≤ 4 * (C * A) + 3 * K ^ 2 := by positivity
      have := pow_le_pow_left₀ h0 hge 2
      nlinarith [mul_pos hCA hCA]
    have : 0 < 4 * C * Rh := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  · have h3 : 3 * K ^ 2 ≤ z := by
      apply le_of_sq_le' hz0
      nlinarith [mul_nonneg hCA.le (sq_nonneg K)]
    have : 4 * C * Rh ≤ 4 * C * A := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  · have hroot := r3_root C A K Rh z T hT hz hR
    exact (mul_eq_zero.1 hroot).resolve_left (by positivity)

lemma r4_case (C A m Rh s T : ℝ) (hC : 0 < C) (hA : 0 < A) (hm : 0 ≤ m) (hs0 : 0 ≤ s)
    (hT : T = m ^ 2 + 9 * C * A * m) (hs : s ^ 2 = T)
    (hR : 9 * C * Rh = 9 * C * A + 2 * m - 2 * s) :
    0 < Rh ∧ Rh ≤ A ∧ 9 * C * (A - Rh) ^ 2 - 4 * m * Rh = 0 := by
  have hCA : 0 < C * A := mul_pos hC hA
  have hs' : s ^ 2 = m ^ 2 + 9 * (C * A) * m := by rw [hs, hT]; ring
  refine ⟨?_, ?_, ?_⟩
  · have hlt : 2 * s < 9 * (C * A) + 2 * m := by
      by_contra hcon
      have hge := not_lt.mp hcon
      have h0 : 0 ≤ 9 * (C * A) + 2 * m := by positivity
      have := pow_le_pow_left₀ h0 hge 2
      nlinarith [mul_pos hCA hCA]
    have : 0 < 9 * C * Rh := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  · have h3 : m ≤ s := by
      apply le_of_sq_le' hs0
      nlinarith [mul_nonneg hCA.le hm]
    have : 9 * C * Rh ≤ 9 * C * A := by linarith
    exact le_of_mul_le_mul_left this (by positivity)
  · have hroot := r4_root C A m Rh s T hT hs hR
    exact (mul_eq_zero.1 hroot).resolve_left (by positivity)

set_option maxHeartbeats 1000000 in
lemma hat2 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (h2 : ¬ δ ≤ delta2 a φ c rf) :
    0 < c * (1 + r3 a δ φ c rf) ∧ c * (1 + r3 a δ φ c rf) ≤ (a + δ) * (1 - φ) ∧
      G (1 - φ) (c * (1 + rf)) (a * (1 - φ)) ((a + δ) * (1 - φ))
        ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) (c * (1 + r3 a δ φ c rf)) =
        K0 a φ c rf ^ 2 / (8 * (1 - φ)) := by
  have hk : 0 < 1 - φ := by linarith
  have ha : 0 < a := by linarith
  have hu : 0 < 1 + rf := by linarith
  have hu' : 0 < rf + 1 := by linarith
  have hcu : 0 < c * (1 + rf) := by positivity
  have hK : 0 < K0 a φ c rf := by unfold K0; linarith
  have hKe : K0 a φ c rf = (1 - φ) * a - c * (1 + rf) := rfl
  have hK' : 0 < a * (1 - φ) - c * (1 + rf) := by rw [hKe] at hK; linarith
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have s6a := sqrt6_gt
  have hkδ := mul_pos hk hδ
  have hApos : 0 < (a + δ) * (1 - φ) := mul_pos (by linarith) hk
  have hbd : 12 * (a * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2
      = 8 * ((a + δ) * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2 := by
    linear_combination (4 * (1 - φ) ^ 2 * δ ^ 2) * hs6
  have hd2 : K0 a φ c rf < (Real.sqrt 6 + 2) * (1 - φ) * δ := by
    unfold delta2 at h2
    rw [not_le, div_lt_iff₀ (by positivity)] at h2
    linarith
  have hd2' : a * (1 - φ) - c * (1 + rf) < (Real.sqrt 6 + 2) * (1 - φ) * δ := by
    rw [hKe] at hd2; linarith
  have hR1C : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) ≤ c * (1 + rf) := by linarith
  have hR1A : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) ≤ (a + δ) * (1 - φ) := by
    have := mul_pos hkδ (by linarith : (0:ℝ) < 3 + Real.sqrt 6)
    linarith
  have hAR1 : ((a + δ) * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2
      = (15 + 6 * Real.sqrt 6) * (1 - φ) ^ 2 * δ ^ 2 := by
    linear_combination ((1 - φ) ^ 2 * δ ^ 2) * hs6
  have hh := caseB_hh (1 - φ) δ (c * (1 + rf)) (a * (1 - φ) - c * (1 + rf))
    ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ((a + δ) * (1 - φ)) (Real.sqrt 6) hcu
    hK' hd2' hR1C hs6 hAR1
  set T := 3 * a ^ 2 * (1 - φ) ^ 2 + 3 * c ^ 2 * (rf + 1) ^ 2
      + (2 * a * c + 8 * c * δ) * (rf + 1) * (1 - φ) with hTdef
  have hle : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) / c - 1 ≤ r3 a δ φ c rf := by
    unfold r3
    refine r3_ge a δ (1 - φ) c (1 + rf) ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) _ _ _
      T ha hδ hk hc hu hK'.le hR1A hh rfl (by rw [hTdef]; ring) ?_ ?_
    · ring
    · ring
  have hR0le : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) ≤ c * (1 + r3 a δ φ c rf) := by
    have : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) / c ≤ 1 + r3 a δ φ c rf := by linarith
    rw [div_le_iff₀ hc] at this; linarith
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hTe : T = 8 * (c * (1 + rf)) * ((a + δ) * (1 - φ)) + 3 * (a * (1 - φ) - c * (1 + rf)) ^ 2 := by
    rw [hTdef]; ring
  have hz : (Real.sqrt 3 * (a * (1 - φ) - c * (1 + rf)) * Real.sqrt T) ^ 2
      = 3 * (a * (1 - φ) - c * (1 + rf)) ^ 2 * T := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hT0]
  have hz0 : 0 ≤ Real.sqrt 3 * (a * (1 - φ) - c * (1 + rf)) * Real.sqrt T := by positivity
  have hD : 4 * c ^ 2 * (rf + 1) ≠ 0 := by positivity
  have hr3 : r3 a δ φ c rf * (4 * c ^ 2 * (rf + 1)) =
      3 * a ^ 2 * (1 - φ) ^ 2 + 3 * c ^ 2 * (rf + 1) ^ 2 - 2 * c * (a - 2 * δ) * (rf + 1) * (1 - φ)
        - 4 * c ^ 2 * (rf + 1) - Real.sqrt 3 * (a * (1 - φ) - c * (1 + rf)) * Real.sqrt T := by
    unfold r3; rw [div_mul_cancel₀ _ hD]
  have hRh : 4 * (c * (1 + rf)) * (c * (1 + r3 a δ φ c rf))
      = 4 * (c * (1 + rf)) * ((a + δ) * (1 - φ)) + 3 * (a * (1 - φ) - c * (1 + rf)) ^ 2
        - Real.sqrt 3 * (a * (1 - φ) - c * (1 + rf)) * Real.sqrt T := by
    linear_combination hr3
  obtain ⟨hRh0, hRhA, hroot⟩ := r3_case (c * (1 + rf)) ((a + δ) * (1 - φ))
    (a * (1 - φ) - c * (1 + rf)) (c * (1 + r3 a δ φ c rf)) _ T hcu hApos hz0 hTe hz hRh
  refine ⟨hRh0, hRhA, ?_⟩
  rw [G_branch2 _ _ _ _ _ _ hk hRh0 hR0le hbd, hKe,
    div_eq_div_iff (mul_pos (mul_pos (by norm_num) hk) hRh0).ne' (mul_pos (by norm_num) hk).ne']
  linear_combination (4 * (1 - φ)) * hroot

set_option maxHeartbeats 1000000 in
lemma hat3 (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (h1 : ¬ δ ≤ delta1 a φ c rf) :
    0 < c * (1 + r4 a δ φ c rf) ∧ c * (1 + r4 a δ φ c rf) ≤ (a + δ) * (1 - φ) ∧
      G (1 - φ) (c * (1 + rf)) (a * (1 - φ)) ((a + δ) * (1 - φ))
        ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) (c * (1 + r4 a δ φ c rf)) =
        δ * Kfun a δ φ c rf / 27 := by
  have hk : 0 < 1 - φ := by linarith
  have hu : 0 < 1 + rf := by linarith
  have hcu : 0 < c * (1 + rf) := by positivity
  have hK : 0 < K0 a φ c rf := by unfold K0; linarith
  have hKe : K0 a φ c rf = (1 - φ) * a - c * (1 + rf) := rfl
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have s6a := sqrt6_gt
  have h21 := delta21 a φ c rf hφ1 hK
  have hkδ := mul_pos hk hδ
  have hApos : 0 < (a + δ) * (1 - φ) := mul_pos (by linarith) hk
  have hA : 0 ≤ (a + δ) * (1 - φ) := hApos.le
  obtain ⟨hS1, hS, hKf⟩ := S_facts a δ φ c rf hδ hφ1 hK
  have hm : 0 ≤ δ * (1 - φ) * Kfun a δ φ c rf := by rw [hKf]; positivity
  have hbd : 12 * (a * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2
      = 8 * ((a + δ) * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2 := by
    linear_combination (4 * (1 - φ) ^ 2 * δ ^ 2) * hs6
  have h2 : ¬ δ ≤ delta2 a φ c rf := fun h => h1 (le_trans h h21.le)
  have hd2 : K0 a φ c rf < (Real.sqrt 6 + 2) * (1 - φ) * δ := by
    unfold delta2 at h2
    rw [not_le, div_lt_iff₀ (by positivity)] at h2
    linarith
  have hR1C : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) ≤ c * (1 + rf) := by rw [hKe] at hd2; linarith
  have hR1A : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) ≤ (a + δ) * (1 - φ) := by
    have := mul_pos hkδ (by linarith : (0:ℝ) < 3 + Real.sqrt 6)
    linarith
  have hAR1 : ((a + δ) * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2
      = (15 + 6 * Real.sqrt 6) * (1 - φ) ^ 2 * δ ^ 2 := by
    linear_combination ((1 - φ) ^ 2 * δ ^ 2) * hs6
  have hSb := Sbound a δ φ c rf hδ hφ1 hK (not_le.mp h1)
  have hh := caseC_hh (1 - φ) δ (c * (1 + rf)) ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ))
    ((a + δ) * (1 - φ)) (Sroot a δ φ c rf) (Real.sqrt 6) hk hδ hcu hR1C hS hSb s6a hAR1
  rw [← hKf] at hh
  set T := δ ^ 2 * (1 - φ) ^ 2 * Kfun a δ φ c rf ^ 2
      + 9 * c * δ * (a + δ) * (1 + rf) * (1 - φ) ^ 2 * Kfun a δ φ c rf with hTdef
  have hle : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) / c - 1 ≤ r4 a δ φ c rf := by
    unfold r4
    refine r4_ge c (1 + rf) ((a + δ) * (1 - φ)) (δ * (1 - φ) * Kfun a δ φ c rf)
      ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) _ _ _ T hc hu hA hm hR1A hh rfl ?_ ?_ ?_
    · rw [hTdef]; ring
    · ring
    · ring
  have hR0le : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) ≤ c * (1 + r4 a δ φ c rf) := by
    have : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) / c ≤ 1 + r4 a δ φ c rf := by linarith
    rw [div_le_iff₀ hc] at this; linarith
  have hTe : T = (δ * (1 - φ) * Kfun a δ φ c rf) ^ 2
      + 9 * (c * (1 + rf)) * ((a + δ) * (1 - φ)) * (δ * (1 - φ) * Kfun a δ φ c rf) := by
    rw [hTdef]; ring
  have hT0 : 0 ≤ T := by rw [hTe]; positivity
  have hs : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
  have hD : 9 * c ^ 2 * (1 + rf) ≠ 0 := by positivity
  have hr4 : r4 a δ φ c rf * (9 * c ^ 2 * (1 + rf)) =
      9 * c * (1 + rf) * ((a + δ) * (1 - φ) - c) + 2 * δ * (1 - φ) * Kfun a δ φ c rf
        - 2 * Real.sqrt T := by
    unfold r4; rw [div_mul_cancel₀ _ hD]
  have hRh : 9 * (c * (1 + rf)) * (c * (1 + r4 a δ φ c rf))
      = 9 * (c * (1 + rf)) * ((a + δ) * (1 - φ)) + 2 * (δ * (1 - φ) * Kfun a δ φ c rf)
        - 2 * Real.sqrt T := by
    linear_combination hr4
  obtain ⟨hRh0, hRhA, hroot⟩ := r4_case (c * (1 + rf)) ((a + δ) * (1 - φ))
    (δ * (1 - φ) * Kfun a δ φ c rf) (c * (1 + r4 a δ φ c rf)) _ T hcu hApos hm
    (Real.sqrt_nonneg _) hTe hs hRh
  refine ⟨hRh0, hRhA, ?_⟩
  rw [G_branch2 _ _ _ _ _ _ hk hRh0 hR0le hbd,
    div_eq_div_iff (mul_pos (mul_pos (by norm_num) hk) hRh0).ne' (by norm_num)]
  linear_combination 3 * hroot

lemma hat (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a) :
    0 < c * (1 + rhat2 a δ φ c rf) ∧ c * (1 + rhat2 a δ φ c rf) ≤ (a + δ) * (1 - φ) ∧
      G (1 - φ) (c * (1 + rf)) (a * (1 - φ)) ((a + δ) * (1 - φ))
        ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) (c * (1 + rhat2 a δ φ c rf)) =
        (if δ ≤ delta1 a φ c rf then K0 a φ c rf ^ 2 / (8 * (1 - φ))
         else δ * Kfun a δ φ c rf / 27) := by
  have hk : 0 < 1 - φ := by linarith
  have hcu : 0 < c * (1 + rf) := mul_pos hc (by linarith)
  have hK : 0 < K0 a φ c rf := by unfold K0; linarith
  have hKe : K0 a φ c rf = (1 - φ) * a - c * (1 + rf) := rfl
  have h21 := delta21 a φ c rf hφ1 hK
  have hkδ := mul_pos hk hδ
  unfold rhat2
  by_cases h2 : δ ≤ delta2 a φ c rf
  · have h1 : δ ≤ delta1 a φ c rf := le_trans h2 h21.le
    rw [if_pos h2, if_pos h1]
    have hCR0 : c * (1 + rf) ≤ (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) := by
      unfold delta2 at h2
      rw [le_div_iff₀ (mul_pos (by positivity) hk), hKe] at h2
      linarith
    refine ⟨hcu, by linarith, ?_⟩
    unfold G
    rw [if_pos hCR0, hKe,
      div_eq_div_iff (mul_pos (mul_pos (by norm_num) hk) hcu).ne' (mul_pos (by norm_num) hk).ne']
    ring
  rw [if_neg h2]
  by_cases h1 : δ ≤ delta1 a φ c rf
  · rw [if_pos h1, if_pos h1]
    exact hat2 a δ φ c rf hδ hδa hφ1 hc hrf hprof h2
  · rw [if_neg h1, if_neg h1]
    exact hat3 a δ φ c rf hδ hδa hφ1 hc hrf hprof h1

end PFW5

open PlatformFinance.WinWin in
theorem solution (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    (r < rhat2 a δ φ c rf → supplierProfitT a δ φ c rf σT < supplierProfitP c rf σP) ∧
      (rhat2 a δ φ c rf ≤ r → supplierProfitP c rf σP ≤ supplierProfitT a δ φ c rf σT) := by
  have hk : 0 < 1 - φ := by linarith
  have hcu : 0 < c * (1 + rf) := mul_pos hc (by linarith)
  have hR : 0 < c * (1 + r) := mul_pos hc (by linarith)
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hbd : 12 * (a * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2
      = 8 * ((a + δ) * (1 - φ) - (1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ^ 2 := by
    linear_combination (4 * (1 - φ) ^ 2 * δ ^ 2) * hs6
  have hR0M : (1 - φ) * (a - (Real.sqrt 6 + 2) * δ) < a * (1 - φ) := by
    have := mul_pos (mul_pos hk hδ) (by positivity : (0:ℝ) < Real.sqrt 6 + 2)
    linarith
  have hPP := PFW5.PiP a δ φ c rf r hφ1 hc hr _
    (profits_P a δ φ c rf hδ hδa hφ0 hφ1 hc hrf hprof r hr hrq σP hP).2
  obtain ⟨hRh0, hRhA, hG⟩ := PFW5.hat a δ φ c rf hδ hδa hφ1 hc hrf hprof
  have hTT := (profits_T a δ φ c rf hδ hδa hφ0 hφ1 hc hrf hprof σT hT).2
  rw [← hG] at hTT
  rw [hPP, hTT]
  constructor
  · intro h
    have hlt : c * (1 + r) < c * (1 + rhat2 a δ φ c rf) := by nlinarith
    exact (PFW5.G_anti _ _ _ _ _ _ _ hk hcu hR0M hbd hR hlt.le hRhA).2 hlt
  · intro h
    have hle : c * (1 + rhat2 a δ φ c rf) ≤ c * (1 + r) := by nlinarith
    exact (PFW5.G_anti _ _ _ _ _ _ _ hk hcu hR0M hbd hRh0 hle hrq.le).1
