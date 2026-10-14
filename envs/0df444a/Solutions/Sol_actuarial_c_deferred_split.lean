-- Prove2me | solution 1 for actuarial_c_deferred_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T07:47:34.082834+00:00
-- url     : https://prove2.me/submissions/293b1a5e-2346-4cff-8e96-350a92920bb7

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_deferred

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialAssurances

theorem solution (h a n : ℕ) (v : ℝ) (b p : ℕ → ℝ)
    (han : a+n ≤ h) :
    term h (a+n) v b p = term h a v b p +
      deferred h a n v b p := by
  have hterm_mass (m : ℕ) (hm : m ≤ h) :
      term h m v b p =
      ∑ j ∈ Finset.range m, v^(j+1)*b j*p j := by
    unfold term termPath
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    have hcover : j < h :=
      lt_of_lt_of_le (Finset.mem_range.mp hj) hm
    simp only [if_pos hcover]
    have hjmem : j ∈ Finset.range (h + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_lt hcover)
    calc
      (∑ k ∈ Finset.range (h+1),
        p k * (v^(j+1) * b j * death k j)) =
        ∑ k ∈ Finset.range (h+1),
          if k = j then p k * (v^(j+1) * b j) else 0 := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkj : k = j <;> simp [death, hkj]
      _ = p j * (v^(j+1) * b j) := by simp [hjmem]
      _ = v^(j+1)*b j*p j := by ring
  have hslice (f : ℕ → ℝ) :
      (∑ j ∈ Finset.range h,
          if a ≤ j ∧ j < a+n then f j else 0) =
        ∑ j ∈ Finset.range n, f (a+j) := by
    have hfilter : (Finset.range h).filter
        (fun j => a ≤ j ∧ j < a+n) = Finset.Ico a (a+n) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · intro hj
        exact hj.2
      · intro hj
        exact ⟨lt_of_lt_of_le hj.2 han, hj⟩
    calc
      (∑ j ∈ Finset.range h,
         if a ≤ j ∧ j < a+n then f j else 0) =
        ∑ j ∈ (Finset.range h).filter
          (fun j => a ≤ j ∧ j < a+n), f j := by
            simp [Finset.sum_ite]
      _ = ∑ j ∈ Finset.Ico a (a+n), f j := by rw [hfilter]
      _ = ∑ j ∈ Finset.range n, f (a+j) := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
  have ha : a ≤ h := le_trans (Nat.le_add_right a n) han
  rw [hterm_mass (a+n) han, hterm_mass a ha]
  unfold deferred
  rw [Finset.sum_range_add]
  congr 1
  exact (hslice (fun j => v^(j+1)*b j*p j)).symm
