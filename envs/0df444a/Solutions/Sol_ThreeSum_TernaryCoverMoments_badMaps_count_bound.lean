-- Prove2me | solution 1 for ThreeSum.TernaryCoverMoments.badMaps_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:43.9188+00:00
-- url     : https://prove2.me/submissions/f442e873-5a68-41d0-953a-639af341cc5a

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
import Theorems.Thm_ThreeSum_TernaryCoverMoments_target_bad_count_bound
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
variable {T : Type*} [Fintype T] [DecidableEq T]
namespace ThreeSum.TernaryCoverMoments
theorem _root_.solution (X : Ω → T → ℕ) (k τ C : ℕ)
    (hmoment : ∀ t : T, (∑ w, X w t ^ k) ≤ C * Fintype.card Ω) :
    τ ^ k * (badMaps X τ).card ≤ Fintype.card T * C * Fintype.card Ω := by
  classical
  have hcard : (badMaps X τ).card ≤
      ∑ t : T, (univ.filter fun w => τ < X w t).card := by
    have heq : badMaps X τ =
        (univ : Finset T).biUnion (fun t => univ.filter fun w => τ < X w t) := by
      ext w
      simp [badMaps]
    rw [heq]
    exact card_biUnion_le
  calc
    _ ≤ τ ^ k * ∑ t : T, (univ.filter fun w => τ < X w t).card :=
      Nat.mul_le_mul_left _ hcard
    _ = ∑ t : T, τ ^ k * (univ.filter fun w => τ < X w t).card := mul_sum ..
    _ ≤ ∑ t : T, C * Fintype.card Ω :=
      sum_le_sum (fun t _ => (target_bad_count_bound X k τ t).trans (hmoment t))
    _ = _ := by simp; ring
end ThreeSum.TernaryCoverMoments
