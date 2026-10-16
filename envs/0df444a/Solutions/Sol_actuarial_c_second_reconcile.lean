-- Prove2me | solution 1 for actuarial_c_second_reconcile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T13:13:38.364352+00:00
-- url     : https://prove2.me/submissions/fc6dedf2-1391-4b69-9f08-be9bcae9cd0b

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_secondMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ActuarialAssurances

private theorem path_value_by_year_local (h k : ℕ) (v : ℝ) (b : ℕ → ℝ) :
    path h v b k = if k < h then v^(k+1)*b k else 0 := by
  unfold path
  by_cases hk : k < h
  · have hmem : k ∈ Finset.range h := Finset.mem_range.mpr hk
    calc
      (∑ j ∈ Finset.range h, v^(j+1)*b j*death k j) =
      (∑ j ∈ Finset.range h,
        if j = k then v^(j+1)*b j else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases h : j = k
        · subst j
          simp [death]
        · have hne : k ≠ j := Ne.symm h
          simp [death, h, hne]
      _ = if k < h then v^(k+1)*b k else 0 := by
        simp [hmem, hk]
  · have hz : (∑ j ∈ Finset.range h, v^(j+1)*b j*death k j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hne : k ≠ j := by
        intro he
        apply hk
        simpa [he] using (Finset.mem_range.mp hj)
      simp [death, hne]
    simp [hk, hz]

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) : second h v b p=secondMass h v b p := by
  unfold second secondMass
  rw [Finset.sum_range_succ]
  have hterminal : path h v b h = 0 := by
    rw [path_value_by_year_local]
    simp
  simp only [hterminal, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hkh : k < h := Finset.mem_range.mp hk
  rw [path_value_by_year_local, if_pos hkh]
  rw [mul_pow, ← pow_mul]
  have he : (k+1)*2=2*(k+1) := Nat.mul_comm _ _
  rw [he]
  ring
