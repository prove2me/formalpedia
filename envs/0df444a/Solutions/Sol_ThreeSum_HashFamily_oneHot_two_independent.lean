-- Prove2me | solution 1 for ThreeSum.HashFamily.oneHot_two_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:40.539207+00:00
-- url     : https://prove2.me/submissions/5b791846-09ca-4fbc-ab3d-2ab87a5f4466

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
import Theorems.Thm_ThreeSum_HashFamily_two_relation

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Field K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := two_relation hst (a := g 0) (b := g 1) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ] using hp)
  fin_cases i <;> simp_all
end ThreeSum.HashFamily
