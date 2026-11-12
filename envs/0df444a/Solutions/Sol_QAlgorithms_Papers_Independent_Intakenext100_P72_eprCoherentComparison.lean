-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P72.eprCoherentComparison
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:11:00.189868+00:00
-- url     : https://prove2.me/submissions/5cd40efa-8139-4e40-b869-2144ef2f3ca9

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Intakenext100.P72 in
theorem solution
    (G chi V : ℝ) (hG : 0 < G) (hV : 1 ≤ V)
    (hphysical : |1 - G| ≤ G * chi) :
    eprExpression G chi V = (1 / 4 : ℝ) *
      Real.logb 2 (1 / (G * chi + G / V) ^ 2) ∧
    eprExpression G chi V = (1 / 2 : ℝ) * Real.logb 2 (1 / (G * chi + G / V)) ∧
    coherentExpression G chi V = (1 / 2 : ℝ) *
      Real.logb 2 (1 / ((G * chi + G / V) * (G * chi + G))) ∧
    coherentExpression G chi V = eprExpression G chi V -
      (1 / 2 : ℝ) * Real.logb 2 (G * (1 + chi)) ∧
    coherentExpression G chi V ≤ eprExpression G chi V ∧
    (coherentExpression G chi V = eprExpression G chi V ↔
      G ≤ 1 ∧ G * chi = 1 - G) ∧
    (G ≤ 1 → G * chi = 1 - G →
      eprExpression G chi V = lossExpression G V ∧
      coherentExpression G chi V = lossExpression G V ∧
      0 ≤ lossExpression G V) := by
  have hGc : 0 ≤ G * chi := le_trans (abs_nonneg _) hphysical
  have hVpos : 0 < V := by linarith
  have hGV : 0 < G / V := div_pos hG hVpos
  have hGV' : G / V ≤ G := div_le_self hG.le hV
  have hupos : 0 < G * chi + G / V := by linarith
  have hw : 1 ≤ G * (1 + chi) := by
    have := le_abs_self (1 - G)
    nlinarith
  have hwpos : 0 < G * (1 + chi) := by linarith
  have hE2 : eprExpression G chi V = (1 / 4 : ℝ) *
      Real.logb 2 (1 / (G * chi + G / V) ^ 2) := by
    unfold eprExpression balanceExpression varianceProduct
    rw [show (G * chi + G * (1 / V)) * (G * chi + G / V) = (G * chi + G / V) ^ 2 by ring]
    ring
  have hE1 : eprExpression G chi V = (1 / 2 : ℝ) * Real.logb 2 (1 / (G * chi + G / V)) := by
    rw [hE2, ← one_div_pow, Real.logb_pow]
    push_cast
    ring
  have hC : coherentExpression G chi V = (1 / 2 : ℝ) *
      Real.logb 2 (1 / ((G * chi + G / V) * (G * chi + G))) := by
    unfold coherentExpression balanceExpression varianceProduct
    rw [show (G * chi + G * 1) * (G * chi + G / V) = (G * chi + G / V) * (G * chi + G) by ring]
  have hC2 : coherentExpression G chi V = eprExpression G chi V -
      (1 / 2 : ℝ) * Real.logb 2 (G * (1 + chi)) := by
    have e : (1 / (G * chi + G / V)) * (G * (1 + chi))⁻¹ =
        (1 : ℝ) / ((G * chi + G / V) * (G * chi + G)) := by
      rw [one_div, one_div, ← mul_inv]
      congr 1
      ring
    rw [hC, hE1, ← e,
      Real.logb_mul (one_div_pos.mpr hupos).ne' (inv_ne_zero hwpos.ne'), Real.logb_inv]
    ring
  have hlw : 0 ≤ Real.logb 2 (G * (1 + chi)) := Real.logb_nonneg (by norm_num) hw
  refine ⟨hE2, hE1, hC, hC2, ?_, ?_, ?_⟩
  · rw [hC2]; linarith
  · rw [hC2]
    constructor
    · intro h
      have h0 : Real.logb 2 (G * (1 + chi)) = 0 := by linarith
      have h1 : G * (1 + chi) = 1 := by
        by_contra hne
        have hgt : 1 < G * (1 + chi) := lt_of_le_of_ne hw (Ne.symm hne)
        have := Real.logb_pos (by norm_num : (1:ℝ) < 2) hgt
        linarith
      constructor <;> nlinarith
    · rintro ⟨_, h2⟩
      have h1 : G * (1 + chi) = 1 := by linarith
      rw [h1, Real.logb_one]
      ring
  · intro _ h2
    have h1 : G * (1 + chi) = 1 := by linarith
    have hL : lossExpression G V = (1 / 2 : ℝ) * Real.logb 2 (1 / (G * chi + G / V)) := by
      unfold lossExpression
      rw [show 1 - G * (1 - 1 / V) = G * chi + G / V by rw [h2]; ring]
    have hu1 : G * chi + G / V ≤ 1 := by linarith
    have hge : 1 ≤ 1 / (G * chi + G / V) := by
      rw [le_div_iff₀ hupos]; linarith
    refine ⟨by rw [hE1, hL], by rw [hC2, h1, Real.logb_one, hE1, hL]; ring, ?_⟩
    rw [hL]
    have := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hge
    linarith
