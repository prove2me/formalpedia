-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.pairing_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:56.386124+00:00
-- url     : https://prove2.me/submissions/b9db4a9e-7f3e-4dfe-b67c-666023df09ab

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
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
theorem _root_.solution (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0) :
    Function.Injective (pairing ℓ) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  apply hℓ
  ext z
  have hh := congrArg (fun f : Module.Dual K E => f (z/a)) ha
  simpa [pairing, mul_div_cancel₀, hne, mul_comm, mul_left_comm, mul_assoc] using hh
end ThreeSum.TernaryOriginalRowMenu
