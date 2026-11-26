-- Prove2me | solution 1 for TranslationOuter.final_card_bound_from_k
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:10:44.951873+00:00
-- url     : https://prove2.me/submissions/087e5033-709c-4075-b0ee-c68ba37ea54c

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_GeneralFinalRatio_cutoff_mul_k_le

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationOuter
open GeneralFinalRatio
noncomputable section
universe u
namespace TranslationOuter
theorem _root_.solution
    (d n k good plans : ℕ) (hd : 3 ≤ d) (hkn : k < n)
    (hinc : k * good ≤
      8 * (d - 1) * cutoff d n k * plans) :
    good * k ^ 2 ≤ K d * n * plans := by
  have hcut := cutoff_mul_k_le d n k hkn
  have hcoef : 8 * (d - 1) * (64 * d + 1) ≤ K d := by
    calc
      8 * (d - 1) * (64 * d + 1) ≤ 8 * d * (65 * d) := by
        gcongr <;> omega
      _ = 520 * d ^ 2 := by ring
      _ ≤ 1048576 * d ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = K d := by rfl
  calc
    good * k ^ 2 = (k * good) * k := by ring
    _ ≤ (8 * (d - 1) * cutoff d n k * plans) * k :=
      Nat.mul_le_mul_right k hinc
    _ = 8 * (d - 1) * (cutoff d n k * k) * plans := by ring
    _ ≤ 8 * (d - 1) * ((64 * d + 1) * n) * plans := by
      gcongr
    _ = (8 * (d - 1) * (64 * d + 1)) * n * plans := by ring
    _ ≤ K d * n * plans := by
      gcongr
end TranslationOuter
