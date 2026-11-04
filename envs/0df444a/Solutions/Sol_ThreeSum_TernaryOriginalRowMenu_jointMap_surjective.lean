-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.jointMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:13:00.680325+00:00
-- url     : https://prove2.me/submissions/eb87609b-1953-42bb-b39e-2ca6b1a0ff2f

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_pairing_injective
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
theorem _root_.solution {t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → E) (hv : LinearIndependent K v) :
    Function.Surjective (jointMap ℓ v) := by
  let B := (pairing ℓ).comp (Fintype.linearCombination K v)
  have hi : Function.Injective B := (pairing_injective ℓ hℓ).comp
    hv.fintypeLinearCombination_injective
  have hs := (LinearMap.flip_surjective_iff₁).mpr hi
  intro target
  obtain ⟨y,hy⟩ := hs (dotProductEquiv K (Fin t) target)
  refine ⟨y, ?_⟩
  funext i
  have he := congrArg (fun f : Module.Dual K (Fin t → K) => f (Pi.single i 1)) hy
  simpa [jointMap, B, pairing, Fintype.linearCombination_apply] using he
end ThreeSum.TernaryOriginalRowMenu
