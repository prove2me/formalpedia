-- Prove2me | solution 1 for Size.size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:11:07.927795+00:00
-- url     : https://prove2.me/submissions/82652801-6486-4f54-ac64-23fef32cc012

import Definitions.Def_Bdd_Collect
import Definitions.Def_Bdd_Size
import Theorems.Thm_Size_size_node_le
import Theorems.Thm_Nary_restrict_const
import Theorems.Thm_OBdd_var_lt_high_var
import Theorems.Thm_OBdd_var_lt_low_var
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
namespace Size
private lemma size_le_helper {O : OBdd n m} : size O ≤ 2 ^ (n - O.1.var.1) - 1 := by
  cases O_root_def : O.1.root with
  | terminal b => simp [isTerminal_iff_size_eq_zero.mpr ⟨b, O_root_def⟩]
  | node j =>
    calc _
      _ ≤ 1 + (size (O.low O_root_def)) + (size (O.high O_root_def)) := size_node_le
      _ ≤ 1 + (2 ^ (n - (O.low O_root_def).1.var.1) - 1) + (2 ^ (n - (O.high O_root_def).1.var.1) - 1) := by
        have := size_le_helper (O := O.low O_root_def)
        have := size_le_helper (O := O.high O_root_def)
        omega
      _ ≤ 1 + (2 ^ (n - (O.1.var.1 + 1)) - 1) + (2 ^ (n - (O.high O_root_def).1.var.1) - 1) := by
        simp only [Nat.succ_eq_add_one, add_le_add_iff_right, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        have := OBdd.var_lt_low_var (h := O_root_def)
        simp only [OBdd.var] at this
        omega
      _ ≤ 1 + (2 ^ (n - (O.1.var.1 + 1)) - 1) + (2 ^ (n - (O.1.var.1 + 1)) - 1) := by
        simp only [Nat.succ_eq_add_one, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        have := OBdd.var_lt_high_var (h := O_root_def)
        simp only [OBdd.var] at this
        omega
      _ ≤ 1 + (2 ^ ((n - O.1.var.1) - 1) - 1) + (2 ^ (n - (O.1.var.1 + 1)) - 1) := by
        simp only [Nat.succ_eq_add_one, add_le_add_iff_right, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        omega
      _ ≤ 1 + (2 ^ ((n - O.1.var.1) - 1) - 1) + (2 ^ ((n - O.1.var.1) - 1) - 1) := by
        simp only [Nat.succ_eq_add_one, add_le_add_iff_left, tsub_le_iff_right]
        rw [Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
        apply pow_le_pow_right' (by simp)
        omega
      _ ≤ 2 ^ ((n - O.1.var.1) - 1) + 2 ^ ((n - O.1.var.1) - 1) - 1 := by
        simp only [Nat.succ_eq_add_one]
        have := Nat.one_le_two_pow (n := ((n - O.1.var.1) - 1))
        omega
      _ ≤ 2*2 ^ ((n - O.1.var.1) - 1) - 1 := by omega
      _ ≤ 2 ^ (n - O.1.var.1) - 1 := by
        refine Nat.sub_le_sub_right ?_ 1
        apply le_of_eq
        refine mul_pow_sub_one ?_ 2
        simp [O_root_def]
        omega
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Size
end

set_option autoImplicit true
open Size
namespace Size
theorem _root_.solution {O : OBdd n m} : size O ≤ 2 ^ n - 1 := by
  trans 2 ^ (n - O.1.var.1) - 1
  · exact size_le_helper
  · rw [tsub_le_iff_right, Nat.sub_add_cancel (by exact Nat.one_le_two_pow)]
    apply Nat.pow_le_pow_right <;> omega
end Size
