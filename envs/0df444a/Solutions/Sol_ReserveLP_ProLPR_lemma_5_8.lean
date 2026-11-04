-- Prove2me | solution 1 for ReserveLP.ProLPR.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:37:21.081934+00:00
-- url     : https://prove2.me/submissions/20dd8be3-717b-4c8e-ae88-66b5ef57f0cc

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

open ReserveLP.ProLPR Finset

theorem rlp58_quartic (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 ≤ 1/4 - 9*θ/8 + 21*θ^2/16 - 5*θ^3/96 - 5*θ^4/96 := by
  nlinarith [sq_nonneg (θ - 9/20), mul_nonneg h0 (sub_nonneg.mpr h1),
    mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.mpr h1), mul_nonneg (mul_nonneg h0 h0) h0,
    mul_nonneg (mul_nonneg h0 h0) (sq_nonneg (θ - 9/20))]

theorem rlp58_poly (θ v : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hv0 : 0 ≤ v) (hv : v ≤ θ / 2) :
    1 - v + (θ - θ ^ 2) ≤ 1.25 * (1 - v) * (1 + θ * v / 2 + θ * v ^ 2 / 3) := by
  have hQ := rlp58_quartic θ h0 h1
  have hid : θ * (1.25 * (1 - v) * (1 + θ * v / 2 + θ * v ^ 2 / 3) - (1 - v + (θ - θ ^ 2))) =
      (θ - 2 * v) * (θ - 1/2) ^ 2 + 2 * v * (1/4 - 9*θ/8 + 21*θ^2/16 - 5*θ^3/96 - 5*θ^4/96) +
      θ ^ 2 * v * (θ / 2 - v) * (5/24 + 5/12 * (θ / 2 + v)) := by ring
  rcases h0.lt_or_eq with hθ | hθ
  · have hnn : 0 ≤ (θ - 2 * v) * (θ - 1/2) ^ 2 + 2 * v * (1/4 - 9*θ/8 + 21*θ^2/16 - 5*θ^3/96 - 5*θ^4/96) +
        θ ^ 2 * v * (θ / 2 - v) * (5/24 + 5/12 * (θ / 2 + v)) := by
      have a1 : 0 ≤ (θ - 2 * v) * (θ - 1/2) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have a2 : 0 ≤ 2 * v * (1/4 - 9*θ/8 + 21*θ^2/16 - 5*θ^3/96 - 5*θ^4/96) :=
        mul_nonneg (by linarith) hQ
      have a3 : 0 ≤ θ ^ 2 * v * (θ / 2 - v) * (5/24 + 5/12 * (θ / 2 + v)) := by
        have : 0 ≤ θ / 2 - v := by linarith
        have : 0 ≤ 5/24 + 5/12 * (θ / 2 + v) := by linarith
        positivity
      linarith
    rw [← hid] at hnn
    have := (mul_nonneg_iff_of_pos_left hθ).mp hnn
    linarith
  · subst hθ
    have : v = 0 := by linarith
    subst this; norm_num

theorem rlp58_log (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    v + v ^ 2 / 2 + v ^ 3 / 3 ≤ -Real.log (1 - v) := by
  have habs : |v| < 1 := by rw [abs_of_nonneg hv0]; exact hv1
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have := sum_le_hasSum (range 3) (fun i _ => by positivity) h
  simp [sum_range_succ] at this
  norm_num at this
  linarith

theorem rlp58_cStar : (0.46 : ℝ) < cStar := by
  unfold cStar
  set s := Real.sqrt 2 with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslo : 1.4142 ≤ s := by nlinarith
  have hshi : s ≤ 1.41421357 := by nlinarith
  have habs : |s - 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hb := Real.exp_bound habs (n := 6) (by norm_num)
  have habs' : |s - 2| = 2 - s := by rw [abs_of_neg (by linarith)]; ring
  rw [habs'] at hb
  have hlow := (abs_sub_le_iff.mp hb).2
  simp [sum_range_succ, Nat.factorial] at hlow
  norm_num at hlow
  have hpos : 0 < s - 1 := by linarith
  have key : 2 * (s - 1) * ((1 + (s - 2) + (s - 2) ^ 2 / 2 + (s - 2) ^ 3 / 6 + (s - 2) ^ 4 / 24 +
      (s - 2) ^ 5 / 120) - (2 - s) ^ 6 * (7 / 4320)) = 2663/270 - 359 * s / 54 := by
    linear_combination (-7*s^5/2160 + 127*s^4/2160 - 367*s^3/1080 + 449*s^2/360 - 1427*s/540
      + 881/180) * hs2
  have hR : (0.46 : ℝ) < 2663/270 - 359 * s / 54 := by linarith
  have hexp : (1 + (s - 2) + (s - 2) ^ 2 / 2 + (s - 2) ^ 3 / 6 + (s - 2) ^ 4 / 24 +
      (s - 2) ^ 5 / 120) - (2 - s) ^ 6 * (7 / 4320) ≤ Real.exp (s - 2) := by
    linarith
  calc (0.46 : ℝ) < 2 * (s - 1) * ((1 + (s - 2) + (s - 2) ^ 2 / 2 + (s - 2) ^ 3 / 6 +
        (s - 2) ^ 4 / 24 + (s - 2) ^ 5 / 120) - (2 - s) ^ 6 * (7 / 4320)) := by rw [key]; exact hR
    _ ≤ 2 * (s - 1) * Real.exp (s - 2) := mul_le_mul_of_nonneg_left hexp (by linarith)

theorem solution (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) (hk : 2 ≤ k) :
    OPT2 θ k ≤ 0.46 ∧ (0.46 : ℝ) < cStar := by
  refine ⟨?_, rlp58_cStar⟩
  obtain ⟨h0, h1⟩ := hθ
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  set v := θ / (k : ℝ) with hv
  have hv0 : 0 ≤ v := div_nonneg h0 hkpos.le
  have hvθ : v ≤ θ / 2 := div_le_div_of_nonneg_left h0 (by norm_num) hk2
  have hv1 : v < 1 := by linarith
  have hkv : (k : ℝ) * v = θ := by rw [hv]; field_simp
  have hlog := rlp58_log v hv0 hv1
  have h1v : 0 < 1 - v := by linarith
  have hpow : (1 - v) ^ k ≤ Real.exp (-(θ + (θ * v / 2 + θ * v ^ 2 / 3))) := by
    have e1 : (1 - v) ^ k = Real.exp (k * Real.log (1 - v)) := by
      rw [Real.exp_nat_mul, Real.exp_log h1v]
    rw [e1, Real.exp_le_exp]
    have : (k : ℝ) * (v + v ^ 2 / 2 + v ^ 3 / 3) = θ + (θ * v / 2 + θ * v ^ 2 / 3) := by
      rw [← hkv]; ring
    nlinarith [mul_le_mul_of_nonneg_left hlog hkpos.le]
  set y := θ * v / 2 + θ * v ^ 2 / 3 with hy
  have hy0 : 0 ≤ y := by positivity
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set P := (1 - v) ^ k' with hP
  have hP0 : 0 ≤ P := pow_nonneg h1v.le _
  have hPk : (1 - v) ^ (k' + 1) = P * (1 - v) := pow_succ _ _
  have hOPT : OPT2 θ (k' + 1) = Real.exp (θ - 1) * (P * (1 - v + (θ - θ ^ 2))) := by
    unfold OPT2
    rw [← hv, hPk, Nat.add_sub_cancel]
    ring
  rw [hOPT]
  have hpoly := rlp58_poly θ v h0 h1 hv0 hvθ
  rw [show 1 + θ * v / 2 + θ * v ^ 2 / 3 = 1 + y by rw [hy]; ring] at hpoly
  have he := Real.exp_pos (θ - 1)
  have hstep1 : Real.exp (θ - 1) * (P * (1 - v + (θ - θ ^ 2))) ≤
      Real.exp (θ - 1) * (P * (1.25 * (1 - v) * (1 + y))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly hP0) he.le
  have hPv : P * (1 - v) ≤ Real.exp (-(θ + y)) := by rw [← hPk]; exact hpow
  have hstep2 : Real.exp (θ - 1) * (P * (1.25 * (1 - v) * (1 + y))) ≤
      Real.exp (θ - 1) * (1.25 * Real.exp (-(θ + y)) * (1 + y)) := by
    apply mul_le_mul_of_nonneg_left _ he.le
    have : P * (1.25 * (1 - v) * (1 + y)) = 1.25 * (P * (1 - v)) * (1 + y) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith
  have hstep3 : Real.exp (θ - 1) * (1.25 * Real.exp (-(θ + y)) * (1 + y)) =
      1.25 * Real.exp (-1) * (Real.exp (-y) * (1 + y)) := by
    have : Real.exp (θ - 1) * Real.exp (-(θ + y)) = Real.exp (-1) * Real.exp (-y) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    linear_combination (1.25 * (1 + y)) * this
  have hey : Real.exp (-y) * (1 + y) ≤ 1 := by
    have h := Real.add_one_le_exp y
    have hpos := Real.exp_pos (-y)
    have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hem1 : Real.exp (-1) < (2.7182818283 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_lt_inv₀ (Real.exp_pos 1) (by norm_num)).mpr Real.exp_one_gt_d9
  have hem0 := Real.exp_pos (-1)
  calc Real.exp (θ - 1) * (P * (1 - v + (θ - θ ^ 2)))
      ≤ Real.exp (θ - 1) * (1.25 * Real.exp (-(θ + y)) * (1 + y)) := hstep1.trans hstep2
    _ = 1.25 * Real.exp (-1) * (Real.exp (-y) * (1 + y)) := hstep3
    _ ≤ 1.25 * Real.exp (-1) * 1 := mul_le_mul_of_nonneg_left hey (by positivity)
    _ ≤ 0.46 := by norm_num at hem1 ⊢; linarith
