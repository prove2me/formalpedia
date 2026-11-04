-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.good_y_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:58.938798+00:00
-- url     : https://prove2.me/submissions/b3cd2776-32e8-4fb7-a67f-d4ec38f8c01b

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_jointMap_surjective
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Definitions.Def_WeightedCache3SUM_Alias_a4c88c9d3e341ebb
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
    (v : Fin t → E) (hv : LinearIndependent K v) (target : Fin t → K) :
    Fintype.card K ^ t * (univ.filter fun y => jointMap ℓ v y = target).card =
      Fintype.card E := by
  simpa using HashFamily.linear_fiber_card (jointMap ℓ v)
    (jointMap_surjective ℓ hℓ v hv) target
end ThreeSum.TernaryOriginalRowMenu
