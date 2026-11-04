-- Prove2me | solution 1 for ThreeSum.HashFamily.pairEvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:35.797547+00:00
-- url     : https://prove2.me/submissions/1b69b288-e24f-468d-9a73-5300f4af8a3c

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
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (s t : α → Bool) (a b : K) :
    pairEvent s t a b = wordEvent ![s, t] ![a, b] := by
  ext w
  simp [pairEvent, wordEvent, Fin.forall_fin_succ]
end ThreeSum.HashFamily
