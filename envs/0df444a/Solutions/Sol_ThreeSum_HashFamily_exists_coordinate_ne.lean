-- Prove2me | solution 1 for ThreeSum.HashFamily.exists_coordinate_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:23.608437+00:00
-- url     : https://prove2.me/submissions/80a328c1-bf09-4006-b9a5-0631a17fdc01

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

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra h
  push Not at h
  exact hst (funext h)
end ThreeSum.HashFamily
