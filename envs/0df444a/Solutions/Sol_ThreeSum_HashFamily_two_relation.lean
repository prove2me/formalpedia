-- Prove2me | solution 1 for ThreeSum.HashFamily.two_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:31.250944+00:00
-- url     : https://prove2.me/submissions/b848a486-fdd8-442f-b567-c4c869bb9bb6

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
import Theorems.Thm_ThreeSum_HashFamily_exists_coordinate_ne

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Ring K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t : α → Bool} (hst : s ≠ t) {a b : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have ha := h (i, s i)
  have hb := h (i, t i)
  simpa [oneHot, hi, Ne.symm hi] using And.intro ha hb
end ThreeSum.HashFamily
