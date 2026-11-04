-- Prove2me | solution 1 for ThreeSum.HashFamily.tripleEvent_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:04.519183+00:00
-- url     : https://prove2.me/submissions/0fb825ff-e9dd-42fb-833d-a1333d2b4986

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
import Theorems.Thm_ThreeSum_HashFamily_wordEvent_card

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    Fintype.card K ^ 3 * (wordEvent ![s, t, u] ![a, b, c]).card =
      Fintype.card (α × Bool → K) := by
  apply wordEvent_card
  convert oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl
end ThreeSum.HashFamily
