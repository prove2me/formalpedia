-- Prove2me | solution 1 for SubSuperStoch.SubSpec.deficient_rows_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T02:21:48.865518+00:00
-- url     : https://prove2.me/submissions/cd3abe59-6161-4123-b558-47406183f1e2

import Definitions.Def_SubSuperStoch_SubSpec_Setting
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open Matrix Finset SubSuperStoch.SubSpec

set_option autoImplicit false

namespace D26Deficient

lemma mul_row_bound {n : ℕ} (F G : Matrix (Fin n) (Fin n) ℝ)
    (hF : ∀ i j, 0 ≤ F i j) (hG : ∀ i, rowSum G i ≤ 1) (i : Fin n) :
    rowSum (F * G) i ≤ rowSum F i := by
  change (∑ j, ∑ k, F i k * G k j) ≤ ∑ j, F i j
  rw [sum_comm]
  calc
    ∑ k, ∑ j, F i k * G k j = ∑ k, F i k * ∑ j, G k j := by
      simp only [mul_sum]
    _ ≤ ∑ k, F i k * 1 :=
      sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hG k) (hF i k)
    _ = _ := by simp

lemma power_rows_le_one {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (hF : IsSubStochastic F) (m : ℕ) (i : Fin n) : rowSum (F ^ m) i ≤ 1 := by
  induction m generalizing i with
  | zero => simp [rowSum, Matrix.one_apply]
  | succ m ih =>
      rw [pow_succ']
      exact (mul_row_bound F (F ^ m) hF.1 (fun j => ih j) i).trans (hF.2 i)

end D26Deficient

theorem solution {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (hF : IsSubStochastic F)
    (α₁ : ℝ) (hα₁ : IsGreatest {x | ∃ s, rowSum F s < 1 ∧ x = rowSum F s} α₁)
    (α₂ : ℝ) (hα₂ : IsLeast {x | ∃ i j, 0 < F i j ∧ x = F i j} α₂)
    (C : ℕ) :
    ∀ i, rowSum F i < 1 →
      rowSum (F ^ (C + 1)) i ≤ 1 - (1 - α₁) * α₂ ^ C ∧ 1 - (1 - α₁) * α₂ ^ C < 1 := by
  rcases hα₁.1 with ⟨i₁, hi₁, rfl⟩
  rcases hα₂.1 with ⟨i₂, j₂, hpos, heq⟩
  have hαpos : 0 < α₂ := by simpa [heq] using hpos
  have hentry : F i₂ j₂ ≤ rowSum F i₂ := by
    exact single_le_sum (fun j _ => hF.1 i₂ j) (mem_univ j₂)
  have hαle : α₂ ≤ 1 := by simpa [heq] using hentry.trans (hF.2 i₂)
  have hpowle : α₂ ^ C ≤ 1 := pow_le_one₀ (le_of_lt hαpos) hαle
  have hpowpos : 0 < α₂ ^ C := pow_pos hαpos _
  intro i hi
  have himax : rowSum F i ≤ rowSum F i₁ := hα₁.2 ⟨i, hi, rfl⟩
  constructor
  · calc
      rowSum (F ^ (C + 1)) i ≤ rowSum F i := by
        rw [pow_succ']
        exact D26Deficient.mul_row_bound F (F ^ C) hF.1
          (D26Deficient.power_rows_le_one F hF C) i
      _ ≤ rowSum F i₁ := himax
      _ ≤ 1 - (1 - rowSum F i₁) * α₂ ^ C := by nlinarith
  · nlinarith [mul_pos (sub_pos.mpr hi₁) hpowpos]

#print axioms solution

