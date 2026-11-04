-- Prove2me | solution 1 for ThreeSum.HashFamily.incidenceCount_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:25.745734+00:00
-- url     : https://prove2.me/submissions/b3bf06cd-fbfd-4dd0-b937-216796be547e

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
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
namespace ThreeSum.HashFamily
theorem _root_.solution (events : E → Finset Ω) (w : Ω) :
    incidenceCount events w = ∑ e, if w ∈ events e then (1 : ℕ) else 0 := by
  unfold incidenceCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
end ThreeSum.HashFamily
