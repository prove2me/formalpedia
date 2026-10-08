-- Prove2me | solution 1 for WardropTraffic.Signal.optimum_phase_times
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:05:11.848974+00:00
-- url     : https://prove2.me/submissions/f59cc0e3-4bee-4d87-b5dc-5e15250e25eb

import Mathlib
import Definitions.Def_WardropTraffic_Signal_Setting



namespace WardropTraffic.Signal

lemma wd_core (lam mu a b : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hS0 : 1 < a + b)
    (hx : 2 * lam * a * (a + b - 1) ≤ lam * a ^ 2 + mu * b ^ 2)
    (hy : 2 * mu * b * (a + b - 1) ≤ lam * a ^ 2 + mu * b ^ 2) :
    ∀ z ∈ feasibleXY a b, delayT lam mu a b ≤ delayT lam mu z.1 z.2 := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  have hS0' : 0 < a + b - 1 := by linarith
  have hS : 0 < x + y - 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = (lam * a ^ 2 + mu * b ^ 2) / (a + b - 1) := ⟨_, rfl⟩
  have htS : t * (a + b - 1) = lam * a ^ 2 + mu * b ^ 2 := by
    rw [ht]; field_simp
  have hxt : 2 * lam * a ≤ t := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_right h hS0']
  have hyt : 2 * mu * b ≤ t := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_right h hS0']
  have hh : 0 ≤ lam * x ^ 2 + mu * y ^ 2 - t * (x + y - 1) := by
    nlinarith [mul_nonneg hlam.le (sq_nonneg (x - a)), mul_nonneg hmu.le (sq_nonneg (y - b)),
      mul_nonneg (sub_nonneg.2 hxt) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hyt) (sub_nonneg.2 h2)]
  unfold delayT
  simp only
  rw [div_le_div_iff₀ hS0' hS]
  nlinarith [mul_nonneg hS0'.le hh]

lemma wd_core2 (lam mu a b xi : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hS0 : 1 < a + b)
    (hx : 2 * lam * a * (a + b - 1) = lam * a ^ 2 + mu * b ^ 2)
    (hy : 2 * mu * b * (a + b - 1) ≤ lam * a ^ 2 + mu * b ^ 2) :
    ∀ z ∈ feasibleXY xi b, delayT lam mu a b ≤ delayT lam mu z.1 z.2 := by
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  have hS0' : 0 < a + b - 1 := by linarith
  have hS : 0 < x + y - 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = (lam * a ^ 2 + mu * b ^ 2) / (a + b - 1) := ⟨_, rfl⟩
  have htS : t * (a + b - 1) = lam * a ^ 2 + mu * b ^ 2 := by
    rw [ht]; field_simp
  have hxt : 2 * lam * a = t := by
    have : (2 * lam * a - t) * (a + b - 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hyt : 2 * mu * b ≤ t := by
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_right h hS0']
  have hh : 0 ≤ lam * x ^ 2 + mu * y ^ 2 - t * (x + y - 1) := by
    nlinarith [mul_nonneg hlam.le (sq_nonneg (x - a)), mul_nonneg hmu.le (sq_nonneg (y - b)),
      mul_nonneg (sub_nonneg.2 hyt) (sub_nonneg.2 h2)]
  unfold delayT
  simp only
  rw [div_le_div_iff₀ hS0' hS]
  nlinarith [mul_nonneg hS0'.le hh]

theorem corner_min_core (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hsum : 1 < xi + eta)
    (hx : lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) < 0)
    (hy : mu * eta ^ 2 - lam * xi ^ 2 - 2 * mu * eta * (1 - xi) < 0) :
    ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2 :=
  wd_core lam mu xi eta hlam hmu hsum (by nlinarith) (by nlinarith)

theorem corner_iff_core (lam mu xi eta : ℝ) (hlam : 0 < lam) :
    lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) < 0 ↔ 0 < cornerD lam mu xi eta := by
  have : lam * cornerD lam mu xi eta = -(lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta)) := by
    unfold cornerD; field_simp; ring
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    nlinarith [mul_nonneg hlam.le (neg_nonneg.2 h')]
  · intro h
    nlinarith [mul_pos hlam h]

theorem edgeRoot_eq (lam mu eta : ℝ) (hlam : 0 < lam) (heta : 0 < eta) (hmu : 0 < mu) :
    lam * edgeRoot lam mu eta ^ 2 - mu * eta ^ 2 - 2 * lam * edgeRoot lam mu eta * (1 - eta) = 0 ∧
      1 - eta < edgeRoot lam mu eta := by
  have hq : 0 < (1 - eta) ^ 2 + (mu / lam) * eta ^ 2 := by positivity
  have hs := Real.sq_sqrt hq.le
  have hp := Real.sqrt_pos.2 hq
  unfold edgeRoot
  refine ⟨?_, by linarith⟩
  have : (1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2)) ^ 2 - 2 * (1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2)) * (1 - eta) = mu / lam * eta ^ 2 := by
    nlinarith
  have h2 : lam * ((1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2)) ^ 2 - 2 * (1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2)) * (1 - eta)) = mu * eta ^ 2 := by
    rw [this]; field_simp
  linarith

theorem root_on_edge_core (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hxi0 : 0 < xi) (heta0 : 0 < eta) (hD : cornerD lam mu xi eta < 0) :
    lam * edgeRoot lam mu eta ^ 2 - mu * eta ^ 2 - 2 * lam * edgeRoot lam mu eta * (1 - eta) = 0 ∧
      0 < edgeRoot lam mu eta ∧ edgeRoot lam mu eta < xi ∧
      ∀ x : ℝ, 0 < x → x < xi → lam * x ^ 2 - mu * eta ^ 2 - 2 * lam * x * (1 - eta) = 0 →
        x = edgeRoot lam mu eta := by
  obtain ⟨hE, hgt⟩ := edgeRoot_eq lam mu eta hlam heta0 hmu
  set e := edgeRoot lam mu eta with he
  have hq : 0 < (1 - eta) ^ 2 + (mu / lam) * eta ^ 2 := by positivity
  have hp := Real.sqrt_pos.2 hq
  have hepos : 0 < e := by
    have : e = 1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2) := rfl
    have hs := Real.sq_sqrt hq.le
    nlinarith [sq_nonneg (1 - eta), mul_pos (div_pos hmu hlam) (mul_pos heta0 heta0)]
  have hcorner : lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta) > 0 := by
    have := (corner_iff_core lam mu xi eta hlam)
    by_contra h
    push_neg at h
    rcases h.lt_or_eq with h | h
    · have := this.1 h; linarith
    · have : lam * cornerD lam mu xi eta = -(lam * xi ^ 2 - mu * eta ^ 2 - 2 * lam * xi * (1 - eta)) := by
        unfold cornerD; field_simp; ring
      nlinarith [mul_neg_of_pos_of_neg hlam hD]
  have hs := Real.sq_sqrt hq.le
  have he2 : 2 * (1 - eta) < e := by
    have : e = 1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2) := rfl
    by_contra h
    push_neg at h
    nlinarith [mul_pos (div_pos hmu hlam) (mul_pos heta0 heta0), sq_nonneg (1 - eta)]
  have hlt : e < xi := by
    by_contra h
    push_neg at h
    have : lam * ((xi - e) * (xi + e - 2 * (1 - eta))) > 0 := by nlinarith
    have h3 : 0 < xi + e - 2 * (1 - eta) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 h) h3.le, mul_nonneg hlam.le (mul_nonneg (sub_nonneg.2 h) h3.le)]
  refine ⟨hE, hepos, hlt, ?_⟩
  intro x hx0 hx1 hx
  have : (x - e) * (x + e - 2 * (1 - eta)) = 0 := by
    have : lam * ((x - e) * (x + e - 2 * (1 - eta))) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact h
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exfalso
    have : x + e - 2 * (1 - eta) = 0 := h
    linarith

theorem optimum_core (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hlm : mu ≤ lam) (hxi0 : 0 < xi) (hxi1 : xi < 1) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsum : 1 < xi + eta) :
    (0 < cornerD lam mu xi eta →
        ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2) ∧
      (cornerD lam mu xi eta ≤ 0 →
        (edgeRoot lam mu eta, eta) ∈ feasibleXY xi eta ∧
          ∀ z ∈ feasibleXY xi eta,
            delayT lam mu (edgeRoot lam mu eta) eta ≤ delayT lam mu z.1 z.2) := by
  constructor
  · intro hD
    have hx := (corner_iff_core lam mu xi eta hlam).2 hD
    refine corner_min_core lam mu xi eta hlam hmu hsum hx ?_
    rcases le_or_gt (eta + 2 * xi - 2) 0 with hc | hc
    · nlinarith [mul_nonneg (mul_pos hmu heta0).le (neg_nonneg.2 hc), sq_nonneg xi, mul_pos hxi0 hxi0, mul_pos hlam (mul_pos hxi0 hxi0)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hlm) (mul_pos heta0 hc).le, sq_nonneg (xi - eta),
        mul_pos hlam (mul_pos hxi0 hxi0), mul_pos hlam (mul_pos heta0 (sub_pos.2 heta1))]
  · intro hD
    obtain ⟨hE, hgt⟩ := edgeRoot_eq lam mu eta hlam heta0 hmu
    set e := edgeRoot lam mu eta with he
    have hq : 0 < (1 - eta) ^ 2 + (mu / lam) * eta ^ 2 := by positivity
    have hsq := Real.sq_sqrt hq.le
    have hsd : √((1 - eta) ^ 2 + mu / lam * eta ^ 2) ≤ xi + eta - 1 := by
      apply Real.sqrt_le_iff.2
      refine ⟨by linarith, ?_⟩
      unfold cornerD at hD
      nlinarith
    have hexi : e ≤ xi := by
      have : e = 1 - eta + √((1 - eta) ^ 2 + mu / lam * eta ^ 2) := rfl
      linarith
    have hfeas : (e, eta) ∈ feasibleXY xi eta := ⟨hexi, le_rfl, by simp only; linarith⟩
    refine ⟨hfeas, ?_⟩
    apply wd_core2 lam mu e eta xi hlam hmu (by linarith)
    · nlinarith
    · have : mu * eta ≤ lam * e := by
        have hepos : 0 < e := by linarith
        have h1 : lam * e * eta ≥ mu * eta * eta := by
          nlinarith [mul_nonneg (mul_pos hlam hepos).le (show (0:ℝ) ≤ 2 - eta - e by linarith)]
        nlinarith
      nlinarith

end WardropTraffic.Signal

open WardropTraffic.Signal


theorem solution (lam mu xi eta : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hlm : mu ≤ lam) (hxi0 : 0 < xi) (hxi1 : xi < 1) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hsum : 1 < xi + eta) :
    (0 < cornerD lam mu xi eta →
        ∀ z ∈ feasibleXY xi eta, delayT lam mu xi eta ≤ delayT lam mu z.1 z.2) ∧
      (cornerD lam mu xi eta ≤ 0 →
        (edgeRoot lam mu eta, eta) ∈ feasibleXY xi eta ∧
          ∀ z ∈ feasibleXY xi eta,
            delayT lam mu (edgeRoot lam mu eta) eta ≤ delayT lam mu z.1 z.2) := by
  exact optimum_core lam mu xi eta hlam hmu hlm hxi0 hxi1 heta0 heta1 hsum
