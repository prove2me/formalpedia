-- Prove2me | solution 1 for ThreeSum.HashFamily.pairEvent_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:29.22121+00:00
-- url     : https://prove2.me/submissions/50eb9e6c-2a13-426b-a584-941539436673

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_oneHot_two_independent
import Theorems.Thm_ThreeSum_HashFamily_wordEvent_probability
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_eq

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) (a b : K) :
    eventProbability (pairEvent s t a b) = 1 / (Fintype.card K : ℝ) ^ 2 := by
  rw [pairEvent_eq]
  apply wordEvent_probability
  convert oneHot_two_independent (K := K) hst using 1
  funext i
  fin_cases i <;> rfl
end ThreeSum.HashFamily
