-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.menuEvent_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:01.580044+00:00
-- url     : https://prove2.me/submissions/e9e8f049-4f0f-4033-8167-3e92e0cfe620

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_good_y_fiber_card
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_badSeeds_card_le
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_good_eval_independent
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_card_eq_sum
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
namespace ThreeSum.TernaryOriginalRowMenu
theorem _root_.solution {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K) :
    Fintype.card K ^ t * (menuEvent ℓ v target).card ≤
      Fintype.card E ^ 2 + Fintype.card K ^ t *
        ((Fintype.card K ^ t - 1) * (Λ - 1)) * Fintype.card E := by
  let bad := badSeeds (E := E) v
  let a := Fintype.card K ^ t
  let q := Fintype.card E
  let fiber := fun x : E =>
    (univ.filter fun y : E => jointMap ℓ (fun i => evalVector Λ x (v i)) y = target).card
  have hrow (x : E) : a * fiber x ≤ q + if x ∈ bad then a*q else 0 := by
    by_cases hb : x ∈ bad
    · simp only [if_pos hb]
      have hh : fiber x ≤ q := card_le_card (filter_subset ..)
      exact (Nat.mul_le_mul_left a hh).trans (Nat.le_add_left _ _)
    · have hc := good_y_fiber_card ℓ hℓ _ (good_eval_independent v x hb) target
      simpa only [if_neg hb, add_zero] using hc.le
  have hh : a * (menuEvent ℓ v target).card ≤ q^2 + a*bad.card*q := by
    rw [menuEvent_card_eq_sum, mul_sum]
    calc
      _ ≤ ∑ x : E, (q + if x ∈ bad then a*q else 0) := sum_le_sum fun x _ => hrow x
      _ = _ := by simp [sum_add_distrib, q]; ring
  exact hh.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right q (Nat.mul_le_mul_left a (badSeeds_card_le v hv))) _)
end ThreeSum.TernaryOriginalRowMenu
