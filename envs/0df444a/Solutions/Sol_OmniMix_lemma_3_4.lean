-- Prove2me | solution 1 for OmniMix.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:32:24.080827+00:00
-- url     : https://prove2.me/submissions/b3cc3bef-9766-410d-a92b-e6ddfea4303a

import Mathlib
import Definitions.Def_OmniMix_Feta
import Definitions.Def_OmniMix_Seta
import Definitions.Def_OmniMix_outVal

open OmniMix in
theorem solution (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : Bool) (h : ℝ) (hh0 : -1 ≤ h)
    (hh1 : h ≤ 1) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 2) :
    Feta η p (outVal y) h ≤ 1 + Seta η p h * (outVal y - p) := by
  obtain ⟨K, hK⟩ : ∃ K, K = η ^ 2 * p * (1 - p) * h ^ 2 := ⟨_, rfl⟩
  have hF : ∀ z : ℝ, Feta η p z h = Real.exp (η * h * (z - p)) * Real.exp (-K) := by
    intro z
    unfold Feta
    rw [← Real.exp_add, hK]
    all_goals ring_nf
  have hah : |η * h| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hη0]
    have : |h| ≤ 1 := abs_le.mpr ⟨hh0, hh1⟩
    nlinarith [abs_nonneg h]
  have hb : ∀ q : ℝ, |q| ≤ 1 → |η * h * q| ≤ 1 := by
    intro q hq
    rw [abs_mul]
    nlinarith [abs_nonneg (η * h), abs_nonneg q]
  have hexp : ∀ x : ℝ, |x| ≤ 1 → Real.exp x ≤ 1 + x + x ^ 2 := by
    intro x hx
    have := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
    linarith
  have e1 := hexp _ (hb (1 - p) (by rw [abs_le]; constructor <;> linarith))
  have e0 := hexp _ (hb (0 - p) (by rw [abs_le]; constructor <;> linarith))
  have m1 := mul_le_mul_of_nonneg_left e1 hp0
  have m0 := mul_le_mul_of_nonneg_left e0 (by linarith : (0 : ℝ) ≤ 1 - p)
  have key : p * Real.exp (η * h * (1 - p)) + (1 - p) * Real.exp (η * h * (0 - p)) ≤ 1 + K := by
    rw [hK]; nlinarith
  have hKe : 1 + K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hpos : 0 < Real.exp (-K) := Real.exp_pos _
  have hcancel : Real.exp K * Real.exp (-K) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have key2 : p * Feta η p 1 h + (1 - p) * Feta η p 0 h ≤ 1 := by
    rw [hF, hF]
    have := mul_le_mul_of_nonneg_right (key.trans hKe) hpos.le
    nlinarith
  unfold Seta
  cases y
  · simp only [outVal, Bool.false_eq_true, if_false, if_true, eq_self_iff_true]
    nlinarith
  · simp only [outVal, Bool.false_eq_true, if_false, if_true, eq_self_iff_true]
    nlinarith
