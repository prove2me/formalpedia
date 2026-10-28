-- Prove2me | solution 1 for OrgDiversity.Optimal.success_prob_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:19:24.414527+00:00
-- url     : https://prove2.me/submissions/6c6082c5-6ab7-4000-a024-7582a9de69d7

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace Aux_OrgDiv_SPCF
open OrgDiversity.Optimal

theorem F_pos (P : Params) (hP : P.Standing) (x : ℝ) (hx : 0 < x) : 0 < P.F x := by
  obtain ⟨_, _, _, _, hF0, hFm, _⟩ := hP
  have := hFm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx.le) hx
  rw [hF0] at this
  exact this

theorem F_nonneg (P : Params) (hP : P.Standing) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ P.F x := by
  rcases hx.lt_or_eq with h | h
  · exact (F_pos P hP x h).le
  · rw [← h, hP.2.2.2.2.1]

theorem F_mono (P : Params) (hP : P.Standing) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    P.F x ≤ P.F y :=
  hP.2.2.2.2.2.1.monotoneOn (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy)) hxy

/-- `a ↦ a F(a b)` is strictly increasing on `[0, ∞)` for `b > 0`. -/
theorem m_strict (P : Params) (hP : P.Standing) (b : ℝ) (hb : 0 < b) (a a' : ℝ)
    (ha : 0 ≤ a) (haa' : a < a') : a * P.F (a * b) < a' * P.F (a' * b) := by
  have ha' : 0 < a' := lt_of_le_of_lt ha haa'
  have h1 : P.F (a * b) ≤ P.F (a' * b) :=
    F_mono P hP _ _ (mul_nonneg ha hb.le) (mul_le_mul_of_nonneg_right haa'.le hb.le)
  have h2 : 0 < P.F (a' * b) := F_pos P hP _ (mul_pos ha' hb)
  calc a * P.F (a * b) ≤ a * P.F (a' * b) := mul_le_mul_of_nonneg_left h1 ha
    _ < a' * P.F (a' * b) := mul_lt_mul_of_pos_right haa' h2

theorem m_mono (P : Params) (hP : P.Standing) (b : ℝ) (hb : 0 < b) (a a' : ℝ)
    (ha : 0 ≤ a) (haa' : a ≤ a') : a * P.F (a * b) ≤ a' * P.F (a' * b) := by
  rcases haa'.lt_or_eq with h | h
  · exact (m_strict P hP b hb a a' ha h).le
  · rw [h]

/-- Threshold comparison. -/
theorem thresh (P : Params) (hP : P.Standing) (b1 b2 c : ℝ) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hc : 0 < c) (a0 α : ℝ) (ha0 : 1 / 2 ≤ a0) (ha01 : a0 < 1) (hα : 1 / 2 < α) (hα1 : α ≤ 1)
    (heq : a0 * P.F (a0 * b1) = (1 - a0) * P.F ((1 - a0) * b2) * c) :
    (α ≤ a0 → α * P.F (α * b1) ≤ (1 - α) * P.F ((1 - α) * b2) * c) ∧
    (a0 < α → (1 - α) * P.F ((1 - α) * b2) * c < α * P.F (α * b1)) := by
  constructor
  · intro h
    have g1 := m_mono P hP b1 hb1 α a0 (by linarith) h
    have g2 := m_mono P hP b2 hb2 (1 - a0) (1 - α) (by linarith) (by linarith)
    have g3 := mul_le_mul_of_nonneg_right g2 hc.le
    linarith
  · intro h
    have g1 := m_strict P hP b1 hb1 a0 α (by linarith) h
    have g2 := m_mono P hP b2 hb2 (1 - α) (1 - a0) (by linarith) (by linarith)
    have g3 := mul_le_mul_of_nonneg_right g2 hc.le
    linarith

end Aux_OrgDiv_SPCF

open OrgDiversity.Optimal Aux_OrgDiv_SPCF in
theorem solution (P : Params) (hP : P.Standing) (hA1 : P.Assumption1)
    (αhom αhet : ℝ) (hhom : P.IsAlphaHom αhom) (hhet : P.IsAlphaHet αhet)
    (α k : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1) (hk : 0 < k)
    (πhom πhet : ℝ)
    (hπhom : IsOptimalEffort P .hom α k πhom)
    (hπhet : IsOptimalEffort P .het α k πhet) :
    successProb P .hom α πhom =
      (if α ≤ αhom then
        (1 / 2) * (P.F (P.bH / 2) + πhom * (α * P.F (α * P.bH) +
          (1 - α) * P.F ((1 - α) * P.bH) - P.F (P.bH / 2)))
      else
        (1 / 2) * (P.F (P.bH / 2) + πhom * (α * P.F (α * P.bH) + α * P.F (α * P.bL) -
          P.F (P.bH / 2)))) ∧
    successProb P .het α πhet =
      (if α ≤ αhet then
        (1 / 2) * (P.F (P.bL / 2) + πhet * (α * P.F (α * P.bL) +
          (1 - α) * P.F ((1 - α) * P.bL) - P.F (P.bL / 2)))
      else
        (1 / 2) * (P.F (P.bL / 2) + πhet * (α * P.F (α * P.bL) + α * P.F (α * P.bH) -
          P.F (P.bL / 2)))) := by
  have ⟨hbL, hbLH, hBL, hBLH, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  -- auxiliary facts
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  have hm1 : (1 - α) * P.F ((1 - α) * P.bL) ≤ α * P.F (α * P.bL) :=
    m_mono P hP _ hbL _ _ (by linarith) (by linarith)
  have hmH : (1 - α) * P.F ((1 - α) * P.bH) ≤ α * P.F (α * P.bH) :=
    m_mono P hP _ hbH _ _ (by linarith) (by linarith)
  have hnn : ∀ b, 0 < b → 0 ≤ (1 - α) * P.F ((1 - α) * b) := fun b hb =>
    mul_nonneg (by linarith) (F_nonneg P hP _ (mul_nonneg (by linarith) hb.le))
  have hFLH : α * P.F (α * P.bL) ≤ α * P.F (α * P.bH) :=
    mul_le_mul_of_nonneg_left (F_mono P hP _ _ (by positivity)
      (mul_le_mul_of_nonneg_left hbLH.le (by linarith))) (by linarith)
  have hFLH' : (1 - α) * P.F ((1 - α) * P.bL) ≤ (1 - α) * P.F ((1 - α) * P.bH) :=
    mul_le_mul_of_nonneg_left (F_mono P hP _ _ (mul_nonneg (by linarith) hbL.le)
      (mul_le_mul_of_nonneg_left hbLH.le (by linarith))) (by linarith)
  -- A1 in multiplicative form
  have hA1' : P.F (P.bH / 2) * P.BL ≤ P.BH * P.F (P.bL / 2) := by
    have := hA1
    unfold Params.Assumption1 at this
    rw [div_le_div_iff₀ hFbL2 hBL] at this
    linarith
  constructor
  · -- homogeneous organisation
    have dphi : dStar P .hom α .phi = .one := by
      unfold dStar; rw [if_neg]
      simp only [succ, post, imBen, dmBen, hhalf]; push_neg
      nlinarith [mul_le_mul_of_nonneg_left hFbH2 hBL.le]
    have done : dStar P .hom α .one = .one := by
      unfold dStar; rw [if_neg]
      simp only [succ, post, imBen, dmBen]; push_neg
      have := hnn P.bL hbL
      nlinarith [mul_le_mul_of_nonneg_left (hm1.trans hFLH) hBH.le]
    obtain ⟨⟨ha0, ha01⟩, heq⟩ := hhom
    obtain ⟨tle, tlt⟩ := thresh P hP P.bL P.bH (P.BH / P.BL) hbL hbH hc αhom α ha0.le ha01 hα hα1 heq
    unfold successProb
    rw [dphi, done]
    split_ifs with h
    · have dtwo : dStar P .hom α .two = .one := by
        unfold dStar; rw [if_neg]
        simp only [succ, post, imBen, dmBen]; push_neg
        have := tle h
        have e : (1 - α) * P.F ((1 - α) * P.bH) * (P.BH / P.BL) * P.BL =
            (1 - α) * P.F ((1 - α) * P.bH) * P.BH := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right this hBL.le]
      rw [dtwo]
      simp only [succ, post, imBen]
      ring
    · push_neg at h
      have dtwo : dStar P .hom α .two = .two := by
        unfold dStar; rw [if_pos]
        simp only [succ, post, imBen, dmBen]
        have := tlt h
        have e : (1 - α) * P.F ((1 - α) * P.bH) * (P.BH / P.BL) * P.BL =
            (1 - α) * P.F ((1 - α) * P.bH) * P.BH := by field_simp
        nlinarith [mul_lt_mul_of_pos_right this hBL]
      rw [dtwo]
      simp only [succ, post, imBen]
      ring
  · -- heterogeneous organisation
    have dphi : dStar P .het α .phi = .one := by
      unfold dStar; rw [if_neg]
      simp only [succ, post, imBen, dmBen, hhalf]; push_neg
      nlinarith
    obtain ⟨⟨ha0, ha01⟩, heq⟩ := hhet
    have done : dStar P .het α .one = .one := by
      unfold dStar; rw [if_neg]
      simp only [succ, post, imBen, dmBen]; push_neg
      have g1 := m_mono P hP P.bL hbL (1 / 2) α (by norm_num) hα.le
      have g2 := m_mono P hP P.bH hbH (1 - α) (1 / 2) (by linarith) (by linarith)
      have e1 : (1 / 2 : ℝ) * P.bL = P.bL / 2 := by ring
      have e2 : (1 / 2 : ℝ) * P.bH = P.bH / 2 := by ring
      rw [e1] at g1
      rw [e2] at g2
      have := hnn P.bH hbH
      nlinarith [mul_le_mul_of_nonneg_right g1 hBH.le, mul_le_mul_of_nonneg_right g2 hBL.le]
    obtain ⟨tle, tlt⟩ := thresh P hP P.bH P.bL (P.BH / P.BL) hbH hbL hc αhet α ha0 ha01 hα hα1 heq
    unfold successProb
    rw [dphi, done]
    split_ifs with h
    · have dtwo : dStar P .het α .two = .one := by
        unfold dStar; rw [if_neg]
        simp only [succ, post, imBen, dmBen]; push_neg
        have := tle h
        have e : (1 - α) * P.F ((1 - α) * P.bL) * (P.BH / P.BL) * P.BL =
            (1 - α) * P.F ((1 - α) * P.bL) * P.BH := by field_simp
        nlinarith [mul_le_mul_of_nonneg_right this hBL.le]
      rw [dtwo]
      simp only [succ, post, imBen]
      ring
    · push_neg at h
      have dtwo : dStar P .het α .two = .two := by
        unfold dStar; rw [if_pos]
        simp only [succ, post, imBen, dmBen]
        have := tlt h
        have e : (1 - α) * P.F ((1 - α) * P.bL) * (P.BH / P.BL) * P.BL =
            (1 - α) * P.F ((1 - α) * P.bL) * P.BH := by field_simp
        nlinarith [mul_lt_mul_of_pos_right this hBL]
      rw [dtwo]
      simp only [succ, post, imBen]
      ring
