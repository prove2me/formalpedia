-- Prove2me | solution 1 for ThreeSum.HashFamily.three_relation_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:08:39.420831+00:00
-- url     : https://prove2.me/submissions/28f0abe3-28f0-4b67-9c2d-afee44db9bb3

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
import Theorems.Thm_ThreeSum_HashFamily_two_relation

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Ring K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) {a b c : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have hu : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hu with hu | hu
  · have hb : b = 0 := by
      simpa [oneHot, hi, Ne.symm hi, hu] using h (i, t i)
    have hac : a = 0 ∧ c = 0 := two_relation hsu fun p => by simpa [hb] using h p
    exact ⟨hac.1, hb, hac.2⟩
  · have ha : a = 0 := by
      simpa [oneHot, hi, Ne.symm hi, hu] using h (i, s i)
    have hbc : b = 0 ∧ c = 0 := two_relation htu fun p => by simpa [ha] using h p
    exact ⟨ha, hbc.1, hbc.2⟩
end ThreeSum.HashFamily
