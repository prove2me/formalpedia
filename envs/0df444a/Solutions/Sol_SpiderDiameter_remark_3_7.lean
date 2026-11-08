-- Prove2me | solution 1 for SpiderDiameter.remark_3_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:13:50.37174+00:00
-- url     : https://prove2.me/submissions/137a5012-c7c8-46e9-a9d8-1c4781c34d02

import Mathlib
import Definitions.Def_SpiderDiameter_Candidate

namespace Aux_Spider37

theorem phi_ge (n : ℕ) (hn : 3 ≤ n) (s : ℝ) (hs : 0 ≤ s) : -1 / 2 ≤ SpiderDiameter.phi n s := by
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  unfold SpiderDiameter.phi
  obtain ⟨t, ht⟩ : ∃ t, t = -(2 * s) / ((n:ℝ) - 1) := ⟨_, rfl⟩
  rw [← ht]
  have htm : t * ((n:ℝ) - 1) = -(2 * s) := by rw [ht]; exact div_mul_cancel₀ _ hn1.ne'
  have hexp := Real.add_one_le_exp t
  have hc : 0 ≤ (n:ℝ) * ((n:ℝ) - 2) / 2 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg <;> linarith
  have key : ((n:ℝ) - 1) * (((n:ℝ) - 1) * s + (n:ℝ) * ((n:ℝ) - 2) / 2 * t) = s := by
    linear_combination ((n:ℝ) * ((n:ℝ) - 2) / 2) * htm
  have hX : 0 ≤ ((n:ℝ) - 1) * s + (n:ℝ) * ((n:ℝ) - 2) / 2 * t := by
    have : 0 ≤ ((n:ℝ) - 1) * (((n:ℝ) - 1) * s + (n:ℝ) * ((n:ℝ) - 2) / 2 * t) := by
      rw [key]; exact hs
    exact (mul_nonneg_iff_of_pos_left hn1).mp this
  have h2 := mul_le_mul_of_nonneg_left hexp hc
  nlinarith

end Aux_Spider37

open SpiderDiameter in
theorem solution (n : ℕ) (hn : 3 ≤ n) (y : ℝ) (hy : 0 < y) :
    SpiderDiameter.candidate n (-y) y (-y) = SpiderDiameter.candidate n y y (-y) := by
  unfold SpiderDiameter.candidate
  by_cases hy2 : y < 1 / 2
  · rw [if_pos hy2, if_pos hy2]
    unfold SpiderDiameter.U36
    dsimp only
    rw [if_pos (by linarith : -y < 0), if_neg (by linarith : ¬ y < 0)]
    rw [intervalIntegral.integral_same, intervalIntegral.integral_same]
    ring
  · rw [if_neg hy2, if_neg hy2]
    have hphi : -y ≤ SpiderDiameter.phi n (y - 1 / 2) := by
      have := Aux_Spider37.phi_ge n hn (y - 1 / 2) (by linarith)
      linarith
    rw [if_pos hphi, if_pos hphi]
    unfold SpiderDiameter.U38 SpiderDiameter.finv
    dsimp only
    rw [if_pos (by linarith : -y ≤ -1 / 2)]
    rw [if_pos (⟨by linarith, by linarith⟩ : -y ≤ -y + 1 / 2 ∧ -y + 1 / 2 ≤ 0)]
    rw [if_neg (fun h => by linarith [h.1] : ¬ (y ≤ -y + 1 / 2 ∧ -y + 1 / 2 ≤ 0)),
      if_neg (fun h => by linarith [h.1] : ¬ (y ≤ 0 ∧ 0 ≤ -y + 1 / 2)),
      if_neg (fun h => by linarith [h.2] : ¬ (0 ≤ y ∧ y ≤ -y + 1 / 2)),
      if_neg (fun h => by linarith [h.2] : ¬ (-y + 1 / 2 ≤ y ∧ y ≤ y - 1 / 2))]
    ring
