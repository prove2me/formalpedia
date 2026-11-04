-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.menuEvent_nine_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:05.601213+00:00
-- url     : https://prove2.me/submissions/464470a7-9fa6-43a8-8661-be90c4080fe4

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_card_bound
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
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K)
    (hsize : 8 * Λ * Fintype.card K ^ (2*t) ≤ Fintype.card E) :
    8 * Fintype.card K ^ t * (menuEvent ℓ v target).card ≤ 9 * Fintype.card E ^ 2 := by
  let a := Fintype.card K ^ t
  let q := Fintype.card E
  have hb : (Fintype.card K ^ t - 1) * (Λ - 1) ≤ a*Λ :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hc := menuEvent_card_bound ℓ hℓ v hv target
  have hsize' : 8*Λ*a^2 ≤ q := by
    simpa only [a,q, mul_comm 2 t, pow_mul] using hsize
  have hc' : a * (menuEvent ℓ v target).card ≤ q^2 + a*(a*Λ)*q :=
    hc.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right q (Nat.mul_le_mul_left a hb)) _)
  have hz := Nat.mul_le_mul_right q hsize'
  change 8*a*(menuEvent ℓ v target).card ≤ 9*q^2
  nlinarith
end ThreeSum.TernaryOriginalRowMenu
