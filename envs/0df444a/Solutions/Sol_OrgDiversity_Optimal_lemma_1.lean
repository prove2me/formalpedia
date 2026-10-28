-- Prove2me | solution 1 for OrgDiversity.Optimal.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:18:13.855886+00:00
-- url     : https://prove2.me/submissions/a342f766-3de2-4681-9330-099205debdec

import Mathlib
import Definitions.Def_OrgDiversity_Optimal_Model

namespace Aux_OrgDiv_L1
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


theorem F_strict (P : Params) (hP : P.Standing) (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) :
    P.F x < P.F y :=
  hP.2.2.2.2.2.1 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans hxy.le)) hxy

theorem cont_h (P : Params) (hP : P.Standing) (b1 b2 c : ℝ) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    ContinuousOn (fun a : ℝ => a * P.F (a * b1) - (1 - a) * P.F ((1 - a) * b2) * c)
      (Set.Icc (1 / 2 : ℝ) 1) := by
  have hFc : ContinuousOn P.F (Set.Ici 0) := hP.2.2.2.2.2.2.1
  have c1 : ContinuousOn (fun a : ℝ => P.F (a * b1)) (Set.Icc (1 / 2 : ℝ) 1) :=
    hFc.comp (continuous_id.mul continuous_const).continuousOn
      (fun a ha => Set.mem_Ici.2 (mul_nonneg (by linarith [ha.1]) hb1.le))
  have c2 : ContinuousOn (fun a : ℝ => P.F ((1 - a) * b2)) (Set.Icc (1 / 2 : ℝ) 1) :=
    hFc.comp ((continuous_const.sub continuous_id).mul continuous_const).continuousOn
      (fun a ha => Set.mem_Ici.2 (mul_nonneg (by linarith [ha.2]) hb2.le))
  exact (continuousOn_id.mul c1).sub
    (((continuousOn_const.sub continuousOn_id).mul c2).mul continuousOn_const)


theorem ex_hom (P : Params) (hP : P.Standing) : ∃ a : ℝ, P.IsAlphaHom a := by
  have ⟨hbL, hbLH, hBL, hBLH, hF0, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  have hc1 : 1 < P.BH / P.BL := by rw [one_lt_div hBL]; exact hBLH
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2' : 0 < P.F (P.bH / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  have hcont := cont_h P hP P.bL P.bH (P.BH / P.BL) hbL hbH
  have h0 : (0 : ℝ) ∈ Set.Ioo
      ((fun a : ℝ => a * P.F (a * P.bL) - (1 - a) * P.F ((1 - a) * P.bH) * (P.BH / P.BL)) (1 / 2))
      ((fun a : ℝ => a * P.F (a * P.bL) - (1 - a) * P.F ((1 - a) * P.bH) * (P.BH / P.BL)) 1) := by
    simp only
    constructor
    · have e1 : (1 / 2 : ℝ) * P.bL = P.bL / 2 := by ring
      have e2 : (1 - 1 / 2 : ℝ) * P.bH = P.bH / 2 := by ring
      rw [e1, e2]
      have : P.F (P.bH / 2) < P.F (P.bH / 2) * (P.BH / P.BL) := by
        nlinarith
      nlinarith
    · simp only [sub_self, zero_mul, hF0, mul_zero, one_mul, sub_zero]
      exact F_pos P hP _ hbL
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Ioo (by norm_num) hcont h0
  exact ⟨a, ha, by simp only at hfa; linarith⟩

theorem ex_het (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) :
    ∃ a : ℝ, P.IsAlphaHet a := by
  have ⟨hbL, hbLH, hBL, hBLH, hF0, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  have hc1 : 1 < P.BH / P.BL := by rw [one_lt_div hBL]; exact hBLH
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2' : 0 < P.F (P.bH / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  have hA1' : P.F (P.bH / 2) * P.BL ≤ P.BH * P.F (P.bL / 2) := by
    have := hA1
    unfold Params.Assumption1 at this
    rw [div_le_div_iff₀ hFbL2 hBL] at this
    linarith
  have hA1c : P.F (P.bH / 2) ≤ P.F (P.bL / 2) * (P.BH / P.BL) := by
    rw [mul_div_assoc', le_div_iff₀ hBL]; linarith
  have hcont := cont_h P hP P.bH P.bL (P.BH / P.BL) hbH hbL
  have h0 : (0 : ℝ) ∈ Set.Ico
      ((fun a : ℝ => a * P.F (a * P.bH) - (1 - a) * P.F ((1 - a) * P.bL) * (P.BH / P.BL)) (1 / 2))
      ((fun a : ℝ => a * P.F (a * P.bH) - (1 - a) * P.F ((1 - a) * P.bL) * (P.BH / P.BL)) 1) := by
    simp only
    constructor
    · have e1 : (1 / 2 : ℝ) * P.bH = P.bH / 2 := by ring
      have e2 : (1 - 1 / 2 : ℝ) * P.bL = P.bL / 2 := by ring
      rw [e1, e2]
      linarith
    · simp only [sub_self, zero_mul, hF0, mul_zero, one_mul, sub_zero]
      exact F_pos P hP _ hbH
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Ico (by norm_num) hcont h0
  exact ⟨a, ha, by simp only at hfa; linarith⟩

theorem order_lem (P : Params) (hP : P.Standing) (αhom αhet : ℝ) (hhom : P.IsAlphaHom αhom)
    (hhet : P.IsAlphaHet αhet) : αhet < αhom := by
  have ⟨hbL, hbLH, hBL, hBLH, hF0, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  have hc1 : 1 < P.BH / P.BL := by rw [one_lt_div hBL]; exact hBLH
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2' : 0 < P.F (P.bH / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  obtain ⟨⟨ho0, ho1⟩, heqo⟩ := hhom
  obtain ⟨⟨he0, he1⟩, heqe⟩ := hhet
  by_contra hcon
  push Not at hcon
  have hpos : 0 < αhet := by linarith
  have s1 : αhet * P.F (αhet * P.bL) < αhet * P.F (αhet * P.bH) :=
    mul_lt_mul_of_pos_left (F_strict P hP _ _ (by positivity)
      (mul_lt_mul_of_pos_left hbLH hpos)) hpos
  have s2 : (1 - αhet) * P.F ((1 - αhet) * P.bL) ≤ (1 - αhet) * P.F ((1 - αhet) * P.bH) :=
    mul_le_mul_of_nonneg_left (F_mono P hP _ _ (mul_nonneg (by linarith) hbL.le)
      (mul_le_mul_of_nonneg_left hbLH.le (by linarith))) (by linarith)
  have s3 := mul_le_mul_of_nonneg_right s2 hc.le
  rcases eq_or_lt_of_le hcon with h | h
  · rw [h] at heqo
    linarith
  · obtain ⟨_, tlt⟩ := thresh P hP P.bL P.bH (P.BH / P.BL) hbL hbH hc αhom αhet ho0.le ho1
      (by linarith) he1.le heqo
    have := tlt h
    linarith

theorem d_basic (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) (α : ℝ) (hα : 1 / 2 < α)
    (hα1 : α ≤ 1) :
    dStar P .hom α .phi = .one ∧ dStar P .het α .phi = .one ∧
    dStar P .hom α .one = .one ∧ dStar P .het α .one = .one := by
  have ⟨hbL, hbLH, hBL, hBLH, hF0, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  have hc1 : 1 < P.BH / P.BL := by rw [one_lt_div hBL]; exact hBLH
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2' : 0 < P.F (P.bH / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  have hA1' : P.F (P.bH / 2) * P.BL ≤ P.BH * P.F (P.bL / 2) := by
    have := hA1
    unfold Params.Assumption1 at this
    rw [div_le_div_iff₀ hFbL2 hBL] at this
    linarith
  have hm1 : (1 - α) * P.F ((1 - α) * P.bL) ≤ α * P.F (α * P.bL) :=
    m_mono P hP _ hbL _ _ (by linarith) (by linarith)
  have hnn : ∀ b, 0 < b → 0 ≤ (1 - α) * P.F ((1 - α) * b) := fun b hb =>
    mul_nonneg (by linarith) (F_nonneg P hP _ (mul_nonneg (by linarith) hb.le))
  have hFLH : α * P.F (α * P.bL) ≤ α * P.F (α * P.bH) :=
    mul_le_mul_of_nonneg_left (F_mono P hP _ _ (by positivity)
      (mul_le_mul_of_nonneg_left hbLH.le (by linarith))) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold dStar; rw [if_neg]
    simp only [succ, post, imBen, dmBen, hhalf]; push Not
    nlinarith [mul_le_mul_of_nonneg_left hFbH2 hBL.le]
  · unfold dStar; rw [if_neg]
    simp only [succ, post, imBen, dmBen, hhalf]; push Not
    nlinarith
  · unfold dStar; rw [if_neg]
    simp only [succ, post, imBen, dmBen]; push Not
    have := hnn P.bL hbL
    nlinarith [mul_le_mul_of_nonneg_left (hm1.trans hFLH) hBH.le]
  · unfold dStar; rw [if_neg]
    simp only [succ, post, imBen, dmBen]; push Not
    have g1 := m_mono P hP P.bL hbL (1 / 2) α (by norm_num) hα.le
    have g2 := m_mono P hP P.bH hbH (1 - α) (1 / 2) (by linarith) (by linarith)
    have e1 : (1 / 2 : ℝ) * P.bL = P.bL / 2 := by ring
    have e2 : (1 / 2 : ℝ) * P.bH = P.bH / 2 := by ring
    rw [e1] at g1
    rw [e2] at g2
    have := hnn P.bH hbH
    nlinarith [mul_le_mul_of_nonneg_right g1 hBH.le, mul_le_mul_of_nonneg_right g2 hBL.le]

theorem d_two_hom (P : Params) (hP : P.Standing) (αhom : ℝ) (hhom : P.IsAlphaHom αhom)
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    (α ≤ αhom → dStar P .hom α .two = .one) ∧ (αhom < α → dStar P .hom α .two = .two) := by
  have ⟨hbL, hbLH, hBL, hBLH, hF0, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  have hc1 : 1 < P.BH / P.BL := by rw [one_lt_div hBL]; exact hBLH
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2' : 0 < P.F (P.bH / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  obtain ⟨⟨ho0, ho1⟩, heqo⟩ := hhom
  obtain ⟨tleo, tlto⟩ := thresh P hP P.bL P.bH (P.BH / P.BL) hbL hbH hc αhom α ho0.le ho1 hα hα1 heqo
  have e : (1 - α) * P.F ((1 - α) * P.bH) * (P.BH / P.BL) * P.BL =
      (1 - α) * P.F ((1 - α) * P.bH) * P.BH := by field_simp
  constructor
  · intro h
    unfold dStar; rw [if_neg]
    simp only [succ, post, imBen, dmBen]; push Not
    have := tleo h
    nlinarith [mul_le_mul_of_nonneg_right this hBL.le]
  · intro h
    unfold dStar; rw [if_pos]
    simp only [succ, post, imBen, dmBen]
    have := tlto h
    nlinarith [mul_lt_mul_of_pos_right this hBL]

theorem d_two_het (P : Params) (hP : P.Standing) (αhet : ℝ) (hhet : P.IsAlphaHet αhet)
    (α : ℝ) (hα : 1 / 2 < α) (hα1 : α ≤ 1) :
    (α ≤ αhet → dStar P .het α .two = .one) ∧ (αhet < α → dStar P .het α .two = .two) := by
  have ⟨hbL, hbLH, hBL, hBLH, hF0, _⟩ := hP
  have hhalf : ∀ x : ℝ, 1 / 2 * x = x / 2 := fun x => by ring
  have hbH : 0 < P.bH := by linarith
  have hBH : 0 < P.BH := by linarith
  have hc : 0 < P.BH / P.BL := div_pos hBH hBL
  have hc1 : 1 < P.BH / P.BL := by rw [one_lt_div hBL]; exact hBLH
  have hFbL2 : 0 < P.F (P.bL / 2) := F_pos P hP _ (by positivity)
  have hFbH2' : 0 < P.F (P.bH / 2) := F_pos P hP _ (by positivity)
  have hFbH2 : P.F (P.bL / 2) ≤ P.F (P.bH / 2) := F_mono P hP _ _ (by positivity) (by linarith)
  obtain ⟨⟨he0, he1⟩, heqe⟩ := hhet
  obtain ⟨tlee, tlte⟩ := thresh P hP P.bH P.bL (P.BH / P.BL) hbH hbL hc αhet α he0 he1 hα hα1 heqe
  have e : (1 - α) * P.F ((1 - α) * P.bL) * (P.BH / P.BL) * P.BL =
      (1 - α) * P.F ((1 - α) * P.bL) * P.BH := by field_simp
  constructor
  · intro h
    unfold dStar; rw [if_neg]
    simp only [succ, post, imBen, dmBen]; push Not
    have := tlee h
    nlinarith [mul_le_mul_of_nonneg_right this hBL.le]
  · intro h
    unfold dStar; rw [if_pos]
    simp only [succ, post, imBen, dmBen]
    have := tlte h
    nlinarith [mul_lt_mul_of_pos_right this hBL]

end Aux_OrgDiv_L1

open OrgDiversity.Optimal Aux_OrgDiv_L1 in
theorem solution (P : Params) (hP : P.Standing) (hA1 : P.Assumption1) :
    (∃ a : ℝ, P.IsAlphaHom a) ∧ (∃ a : ℝ, P.IsAlphaHet a) ∧
    ∀ αhom αhet : ℝ, P.IsAlphaHom αhom → P.IsAlphaHet αhet →
      (1 / 2 ≤ αhet ∧ αhet < αhom ∧ αhom < 1) ∧
      ∀ α : ℝ, 1 / 2 < α → α ≤ 1 →
        (dStar P .hom α .phi = .one ∧ dStar P .het α .phi = .one) ∧
        (α ≤ αhet →
          dStar P .hom α .one = .one ∧ dStar P .hom α .two = .one ∧
          dStar P .het α .one = .one ∧ dStar P .het α .two = .one) ∧
        (αhet < α → α ≤ αhom →
          dStar P .hom α .one = .one ∧ dStar P .hom α .two = .one ∧
          dStar P .het α .one = .one ∧ dStar P .het α .two = .two) ∧
        (αhom < α →
          dStar P .hom α .one = .one ∧ dStar P .hom α .two = .two ∧
          dStar P .het α .one = .one ∧ dStar P .het α .two = .two) := by
  refine ⟨ex_hom P hP, ex_het P hP hA1, ?_⟩
  intro αhom αhet hhom hhet
  have horder := order_lem P hP αhom αhet hhom hhet
  refine ⟨⟨hhet.1.1, horder, hhom.1.2⟩, ?_⟩
  intro α hα hα1
  obtain ⟨dphi_hom, dphi_het, done_hom, done_het⟩ := d_basic P hP hA1 α hα hα1
  obtain ⟨dho_le, dho_gt⟩ := d_two_hom P hP αhom hhom α hα hα1
  obtain ⟨dhe_le, dhe_gt⟩ := d_two_het P hP αhet hhet α hα hα1
  refine ⟨⟨dphi_hom, dphi_het⟩, ?_, ?_, ?_⟩
  · intro h
    exact ⟨done_hom, dho_le (h.trans horder.le), done_het, dhe_le h⟩
  · intro h1 h2
    exact ⟨done_hom, dho_le h2, done_het, dhe_gt h1⟩
  · intro h
    exact ⟨done_hom, dho_gt h, done_het, dhe_gt (horder.trans h)⟩
