-- Prove2me | solution 1 for ThreeSum.HashFamily.oneHot_three_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:40.1945+00:00
-- url     : https://prove2.me/submissions/9082adf9-161f-4749-a5b5-35baf01f89e3

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
import Definitions.Def_WeightedCache3SUM_Alias_4049c0bb9918328c

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Field K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := three_relation hst hsu htu (a := g 0) (b := g 1) (c := g 2) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all
end ThreeSum.HashFamily
