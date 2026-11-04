-- Prove2me | solution 1 for ThreeSum.HashFamily.tripleEvent_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:30.2705+00:00
-- url     : https://prove2.me/submissions/72f34e56-5d9a-4e2b-8951-cadd9e12c29e

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
import Theorems.Thm_ThreeSum_HashFamily_oneHot_three_independent
import Theorems.Thm_ThreeSum_HashFamily_wordEvent_probability

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    eventProbability (wordEvent ![s, t, u] ![a, b, c]) =
      1 / (Fintype.card K : ℝ) ^ 3 := by
  apply wordEvent_probability
  convert oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl
end ThreeSum.HashFamily
