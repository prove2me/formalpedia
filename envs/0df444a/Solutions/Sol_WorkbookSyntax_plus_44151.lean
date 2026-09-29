-- Prove2me | solution 1 for WorkbookSyntax.plus_44151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T13:02:37.928816+00:00
-- url     : https://prove2.me/submissions/4423aba0-8a1c-4a90-87ce-a9f8486493f4

/- InternLM Lean-Workbook, Apache-2.0. The obsolete finite-sum binder syntax is explicitly modernized. -/
import Mathlib
open Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
theorem solution : ∑ k ∈ Finset.Icc (997 : ℕ) 1995, (1 : ℝ) / k < 1   := by
  have hs : Finset.Icc 997 1995 = Finset.Icc 997 999 ∪ Finset.Icc 1000 1995 := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hd : Disjoint (Finset.Icc 997 999) (Finset.Icc 1000 1995) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    simp only [Finset.mem_Icc] at hk hl
    omega
  rw [hs, Finset.sum_union hd]
  have h1 : (∑ k ∈ Finset.Icc (997 : ℕ) 999, (1 : ℝ) / k) ≤ 3 / 997 := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc (997 : ℕ) 999, (1 : ℝ) / 997 := by
        apply Finset.sum_le_sum
        intro k hk
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 997)
        exact_mod_cast (Finset.mem_Icc.mp hk).1
      _ = _ := by norm_num
  have h2 : (∑ k ∈ Finset.Icc (1000 : ℕ) 1995, (1 : ℝ) / k) ≤ 996 / 1000 := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc (1000 : ℕ) 1995, (1 : ℝ) / 1000 := by
        apply Finset.sum_le_sum
        intro k hk
        apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1000)
        exact_mod_cast (Finset.mem_Icc.mp hk).1
      _ = _ := by norm_num
  linarith
example : (∑ k ∈ Finset.Icc (997 : ℕ) 1995, (1 : ℝ) / k < 1) := @solution
#print axioms solution
