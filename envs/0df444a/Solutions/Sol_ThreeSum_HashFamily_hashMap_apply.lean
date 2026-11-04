-- Prove2me | solution 1 for ThreeSum.HashFamily.hashMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:24.736053+00:00
-- url     : https://prove2.me/submissions/f1257e42-bcd6-4f06-8dd1-6cefaeb69d7d

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
variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]
namespace ThreeSum.HashFamily
theorem _root_.solution (v : ι → σ → K) (w : σ → K) (i : ι) :
    hashMap v w i = ∑ x, v i x * w x := by
  classical
  rfl
end ThreeSum.HashFamily
