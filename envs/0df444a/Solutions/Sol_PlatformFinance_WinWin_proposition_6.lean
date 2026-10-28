-- Prove2me | solution 1 for PlatformFinance.WinWin.proposition_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T06:27:17.764907+00:00
-- url     : https://prove2.me/submissions/c299df7c-3369-4a81-b56c-8565582683d5

import Mathlib
import Definitions.Def_PlatformFinance_WinWin_Model
import Theorems.Thm_PlatformFinance_WinWin_proposition_4
import Theorems.Thm_PlatformFinance_WinWin_proposition_5

/-!
Proposition 6 of Huang, Lai, Wang & Xiao (SSRN 4014045, p. 18): reduction to Proposition 4
(`PlatformFinance.WinWin.proposition_4`, the seller's threshold r̂₁) and Proposition 5
(`PlatformFinance.WinWin.proposition_5`, the supplier's threshold r̂₂). The comparison
r̂₁ ≤ r̂₂ is proved here in full (`PFW6.rhat_le`).
-/

set_option autoImplicit false

namespace PFW6
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

lemma caseD_hh (k δ a C S : ℝ) (hk : 0 < k) (hδ : 0 < δ) (hδa : δ < a) (hC : 0 < C)
    (hS : 1 < S) (hSb : S < 3.777)
    (hS1 : δ * k * S ^ 2 = (δ + 3 * a) * k - 3 * C) :
    0 ≤ 9 * C * ((a + δ) * k - k * (a + 3 * δ - 2 * δ * S)) ^ 2
      - 4 * (δ * k * (δ * k * (S - 1) ^ 2 * (2 * S + 1))) * (k * (a + 3 * δ - 2 * δ * S)) := by
  have hb : 9 * C - (2 * S + 1) * (k * (a + 3 * δ - 2 * δ * S))
      = k * (4 - S) * (2 * a - δ * S) := by
    linear_combination 3 * hS1
  have hpos : δ * S ^ 2 < δ + 3 * a := by
    have h3e : k * (δ + 3 * a - δ * S ^ 2) = 3 * C := by linear_combination -hS1
    have h3 : 0 < k * (δ + 3 * a - δ * S ^ 2) := by rw [h3e]; linarith
    exact by nlinarith [h3]
  have h2a : 0 ≤ 2 * a - δ * S := by
    by_cases hS2 : S ≤ 2
    · nlinarith
    · nlinarith [mul_nonneg hδ.le (mul_nonneg (by linarith : (0:ℝ) ≤ 2 * S + 1)
        (by linarith : (0:ℝ) ≤ S - 2))]
  have hb0 : 0 ≤ 9 * C - (2 * S + 1) * (k * (a + 3 * δ - 2 * δ * S)) := by
    rw [hb]; exact mul_nonneg (mul_nonneg hk.le (by linarith)) h2a
  have : 9 * C * ((a + δ) * k - k * (a + 3 * δ - 2 * δ * S)) ^ 2
      - 4 * (δ * k * (δ * k * (S - 1) ^ 2 * (2 * S + 1))) * (k * (a + 3 * δ - 2 * δ * S))
      = 4 * (δ * k) ^ 2 * (S - 1) ^ 2 * (9 * C - (2 * S + 1) * (k * (a + 3 * δ - 2 * δ * S))) := by
    ring
  rw [this]; positivity

set_option maxHeartbeats 1000000 in
lemma rhat_le (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ1 : φ < 1)
    (hc : 0 < c) (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a) :
    rhat1 a δ φ c rf ≤ rhat2 a δ φ c rf := by
  have hk : 0 < 1 - φ := by linarith
  have ha : 0 < a := by linarith
  have hu : 0 < 1 + rf := by linarith
  have hcu : 0 < c * (1 + rf) := by positivity
  have hK : 0 < K0 a φ c rf := by unfold K0; linarith
  have hKe : K0 a φ c rf = (1 - φ) * a - c * (1 + rf) := rfl
  have hK' : 0 < a * (1 - φ) - c * (1 + rf) := by rw [hKe] at hK; linarith
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have s6a := sqrt6_gt
  have h13 := delta13 a φ c rf hφ1 hK
  have hkδ := mul_pos hk hδ
  have hA : 0 ≤ (a + δ) * (1 - φ) := (mul_pos (by linarith) hk).le
  obtain ⟨hS1, hS, hKf⟩ := S_facts a δ φ c rf hδ hφ1 hK
  have hm : 0 ≤ δ * (1 - φ) * Kfun a δ φ c rf := by rw [hKf]; positivity
  unfold rhat1 rhat2
  by_cases h2 : δ ≤ delta2 a φ c rf
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
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
  by_cases h1 : δ ≤ delta1 a φ c rf
  · rw [if_pos h1, if_pos (le_trans h1 h13.le)]
    unfold r1 r3
    have hh := caseB_hh (1 - φ) δ (c * (1 + rf)) (a * (1 - φ) - c * (1 + rf))
      ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) ((a + δ) * (1 - φ)) (Real.sqrt 6) hcu
      hK' hd2' hR1C hs6 hAR1
    refine r3_ge a δ (1 - φ) c (1 + rf) ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) _ _ _
      (3 * a ^ 2 * (1 - φ) ^ 2 + 3 * c ^ 2 * (rf + 1) ^ 2
        + (2 * a * c + 8 * c * δ) * (rf + 1) * (1 - φ))
      ha hδ hk hc hu hK'.le hR1A hh ?_ ?_ ?_ ?_
    · ring
    · ring
    · ring
    · ring
  rw [if_neg h1]
  have hSb := Sbound a δ φ c rf hδ hφ1 hK (not_le.mp h1)
  by_cases h3 : δ ≤ delta3 a φ c rf
  · rw [if_pos h3]
    unfold r1 r4
    have hh := caseC_hh (1 - φ) δ (c * (1 + rf)) ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ))
      ((a + δ) * (1 - φ)) (Sroot a δ φ c rf) (Real.sqrt 6) hk hδ hcu hR1C hS hSb s6a hAR1
    rw [← hKf] at hh
    refine r4_ge c (1 + rf) ((a + δ) * (1 - φ)) (δ * (1 - φ) * Kfun a δ φ c rf)
      ((1 - φ) * (a - (Real.sqrt 6 + 2) * δ)) _ _ _
      (δ ^ 2 * (1 - φ) ^ 2 * Kfun a δ φ c rf ^ 2
        + 9 * c * δ * (a + δ) * (1 + rf) * (1 - φ) ^ 2 * Kfun a δ φ c rf)
      hc hu hA hm hR1A hh ?_ ?_ ?_ ?_
    · ring
    · ring
    · ring
    · ring
  · rw [if_neg h3]
    unfold r2 r4
    have hS1' : δ * (1 - φ) * Sroot a δ φ c rf ^ 2
        = (δ + 3 * a) * (1 - φ) - 3 * (c * (1 + rf)) := by rw [hS1]; ring
    have hh := caseD_hh (1 - φ) δ a (c * (1 + rf)) (Sroot a δ φ c rf) hk hδ hδa hcu hS hSb hS1'
    rw [← hKf] at hh
    have hR2A : (1 - φ) * (a + 3 * δ - 2 * δ * Sroot a δ φ c rf) ≤ (a + δ) * (1 - φ) := by
      have := mul_pos hkδ (sub_pos.2 hS)
      linarith
    refine r4_ge c (1 + rf) ((a + δ) * (1 - φ)) (δ * (1 - φ) * Kfun a δ φ c rf)
      ((1 - φ) * (a + 3 * δ - 2 * δ * Sroot a δ φ c rf)) _ _ _
      (δ ^ 2 * (1 - φ) ^ 2 * Kfun a δ φ c rf ^ 2
        + 9 * c * δ * (a + δ) * (1 + rf) * (1 - φ) ^ 2 * Kfun a δ φ c rf)
      hc hu hA hm hR2A hh ?_ ?_ ?_ ?_
    · ring
    · ring
    · ring
    · ring

end PFW6

open PlatformFinance.WinWin in
theorem solution (a δ φ c rf : ℝ) (hδ : 0 < δ) (hδa : δ < a) (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) (hc : 0 < c)
    (hrf : 0 ≤ rf) (hprof : c * (1 + rf) < (1 - φ) * a)
    (r : ℝ) (hr : -1 < r) (hrq : c * (1 + r) < (a + δ) * (1 - φ))
    (σT σP : Profile) (hT : IsSPET a δ φ c rf σT) (hP : IsSPEP a δ φ c rf r σP) :
    rhat1 a δ φ c rf ≤ rhat2 a δ φ c rf ∧
      (r < rhat1 a δ φ c rf →
        sellerProfitT a δ φ σT < sellerProfitP a δ φ r σP ∧
          supplierProfitT a δ φ c rf σT < supplierProfitP c rf σP) ∧
      (rhat1 a δ φ c rf < r → r < rhat2 a δ φ c rf →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT ∧
          supplierProfitT a δ φ c rf σT < supplierProfitP c rf σP) ∧
      (rhat2 a δ φ c rf < r →
        sellerProfitP a δ φ r σP ≤ sellerProfitT a δ φ σT ∧
          supplierProfitP c rf σP ≤ supplierProfitT a δ φ c rf σT) := by
  have h12 := PFW6.rhat_le a δ φ c rf hδ hδa hφ1 hc hrf hprof
  obtain ⟨p4a, p4b⟩ := proposition_4 a δ φ c rf hδ hδa hφ0 hφ1 hc hrf hprof r hr hrq σT σP hT hP
  obtain ⟨p5a, p5b⟩ := proposition_5 a δ φ c rf hδ hδa hφ0 hφ1 hc hrf hprof r hr hrq σT σP hT hP
  refine ⟨h12, fun h => ⟨p4a h, p5a (lt_of_lt_of_le h h12)⟩,
    fun h1 h2 => ⟨p4b (Or.inl h1), p5a h2⟩,
    fun h => ⟨p4b (Or.inl (lt_of_le_of_lt h12 h)), p5b h.le⟩⟩
