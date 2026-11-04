-- Prove2me | solution 1 for ThreeSum.HashFamily.oneHot_four_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:16:55.157177+00:00
-- url     : https://prove2.me/submissions/92daeefc-c1a3-4dc0-b8f1-73df117a0888

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
import Definitions.Def_WeightedCache3SUM_Alias_c7ec1e9177bb798d

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Field K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u, oneHot v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := four_relation_of_mask_ne hst hsu hsv htu htv huv hm
    (a := g 0) (b := g 1) (c := g 2) (d := g 3) (fun p => by
      have hp := congrFun hg p
      simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all
end ThreeSum.HashFamily
