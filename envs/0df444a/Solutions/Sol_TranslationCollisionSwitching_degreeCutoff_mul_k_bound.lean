-- Prove2me | solution 1 for TranslationCollisionSwitching.degreeCutoff_mul_k_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:27.054145+00:00
-- url     : https://prove2.me/submissions/033d3eac-5b3a-40ca-8027-5dde86ad5694

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution

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
open TranslationCollisionSwitching
open TranslationReversal TranslationIntegration
noncomputable section
variable {V : Type*} [Fintype V]
variable {d : ℕ} [NeZero d]
variable (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
attribute [local instance] TranslationCollisionSwitching.graphAdjDecidable
attribute [local instance] TranslationCollisionSwitching.vertexDecidableEq
namespace TranslationCollisionSwitching
theorem _root_.solution {n k : ℕ} (hkn : k < n) :
    8 * degreeCutoff d n k * (d - 1) * k ≤ 1024 * d ^ 2 * n := by
  have hdiv : (64 * d * n / k) * k ≤ 64 * d * n :=
    Nat.div_mul_le_self _ _
  calc
    8 * degreeCutoff d n k * (d - 1) * k ≤
        8 * degreeCutoff d n k * d * k := by
      gcongr <;> omega
    _ = 8 * d * ((64 * d * n / k) * k + k) := by
      simp [degreeCutoff]
      ring
    _ ≤ 8 * d * (64 * d * n + n) := by
      gcongr
    _ ≤ 1024 * d ^ 2 * n := by
      calc
        8 * d * (64 * d * n + n) =
            512 * d ^ 2 * n + 8 * d * n := by ring
        _ ≤ 512 * d ^ 2 * n + 8 * d ^ 2 * n := by
          gcongr
          simpa [pow_two] using Nat.le_mul_of_pos_right d (NeZero.pos d)
        _ = 520 * (d ^ 2 * n) := by ring
        _ ≤ 1024 * (d ^ 2 * n) := by gcongr <;> omega
        _ = 1024 * d ^ 2 * n := by ring
end TranslationCollisionSwitching
