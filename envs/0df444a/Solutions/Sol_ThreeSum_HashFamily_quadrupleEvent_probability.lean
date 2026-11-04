-- Prove2me | solution 1 for ThreeSum.HashFamily.quadrupleEvent_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:44.778221+00:00
-- url     : https://prove2.me/submissions/b684652f-0bbb-4e47-ba0a-c9d1e53d530f

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
import Theorems.Thm_ThreeSum_HashFamily_oneHot_four_independent
import Theorems.Thm_ThreeSum_HashFamily_wordEvent_probability

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b c d : K) :
    eventProbability (wordEvent ![s, t, u, v] ![a, b, c, d]) =
      1 / (Fintype.card K : ℝ) ^ 4 := by
  apply wordEvent_probability
  convert oneHot_four_independent (K := K) hst hsu hsv htu htv huv hm using 1
  funext i
  fin_cases i <;> rfl
end ThreeSum.HashFamily
