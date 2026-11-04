-- Prove2me | solution 1 for ThreeSum.TernaryCoverMoments.removed_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:52.617654+00:00
-- url     : https://prove2.me/submissions/a9f46ca8-87ac-44e2-80a6-50c8ed455c34

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace ThreeSum.TernaryCoverMoments
theorem _root_.solution (f : Ω → ℕ) (bad : Finset Ω) (B : ℕ)
    (hcap : ∀ w, f w ≤ B ^ 2) :
    (∑ w ∈ bad, f w) ≤ B ^ 2 * bad.card := by
  calc
    _ ≤ ∑ _w ∈ bad, B ^ 2 := sum_le_sum (fun w _ => hcap w)
    _ = _ := by simp [Nat.mul_comm]
end ThreeSum.TernaryCoverMoments
