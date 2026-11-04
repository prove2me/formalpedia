-- Prove2me | solution 1 for ThreeSum.HashFamily.wordEvent_eq_linear_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:53.035207+00:00
-- url     : https://prove2.me/submissions/01fb1a80-a9ad-41c0-be13-7258c7a40164

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
import Theorems.Thm_ThreeSum_HashFamily_hashValue_family
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {r : ℕ}
    (words : Fin r → α → Bool) (target : Fin r → K) :
    wordEvent words target =
      Finset.univ.filter (fun w => hashMap (fun i => oneHot (K := K) (words i)) w = target) := by
  ext w
  simp only [wordEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hashValue_family]
  exact funext_iff.symm
end ThreeSum.HashFamily
