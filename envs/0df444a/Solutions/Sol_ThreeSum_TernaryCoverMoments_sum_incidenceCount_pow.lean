-- Prove2me | solution 1 for ThreeSum.TernaryCoverMoments.sum_incidenceCount_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:48.555187+00:00
-- url     : https://prove2.me/submissions/115d3388-8282-434d-b40f-f2a41fc53efd

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_incidenceCount_eq_sum
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
namespace ThreeSum.TernaryCoverMoments
theorem _root_.solution (events : E → Finset Ω) (k : ℕ) :
    (∑ w, HashFamily.incidenceCount events w ^ k) =
      ∑ es : Fin k → E, (jointEvent events es).card := by
  classical
  simp_rw [HashFamily.incidenceCount_eq_sum, Fintype.sum_pow, Fintype.prod_boole]
  rw [sum_comm]
  apply sum_congr rfl
  intro es _
  unfold jointEvent
  rw [card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro w _
  by_cases h : ∀ i, w ∈ events (es i) <;> simp [h]
end ThreeSum.TernaryCoverMoments
