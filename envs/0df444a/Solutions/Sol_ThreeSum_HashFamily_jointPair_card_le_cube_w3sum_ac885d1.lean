-- Prove2me | solution 1 for ThreeSum.HashFamily.jointPair_card_le_cube_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:13.119894+00:00
-- url     : https://prove2.me/submissions/1bfa62aa-f4ce-4d84-80eb-4b1033167b8c

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
import Theorems.Thm_ThreeSum_HashFamily_tripleEvent_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsv : s ≠ v) (htu : t ≠ u) (huv : u ≠ v)
    (hpair : (s, t) ≠ (u, v)) (a b : K) :
    Fintype.card K ^ 3 * (pairEvent s t a b ∩ pairEvent u v a b).card ≤
      Fintype.card (α × Bool → K) := by
  by_cases hsu : s = u
  · have htv : t ≠ v := by
      intro htv
      exact hpair (Prod.ext hsu htv)
    have hsub : pairEvent s t a b ∩ pairEvent u v a b ⊆
        wordEvent ![s, t, v] ![a, b, b] := by
      intro w hw
      simpa [wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).2)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (tripleEvent_card hst hsv htv a b b)
  · have hsub : pairEvent s t a b ∩ pairEvent u v a b ⊆
        wordEvent ![s, t, u] ![a, b, a] := by
      intro w hw
      simpa [wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).1)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (tripleEvent_card hst hsu htu a b a)
end ThreeSum.HashFamily
