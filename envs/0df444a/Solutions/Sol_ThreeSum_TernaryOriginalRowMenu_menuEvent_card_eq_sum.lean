-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.menuEvent_card_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:58.47141+00:00
-- url     : https://prove2.me/submissions/4427a121-0bb3-4bfe-ab69-308630eb1c28

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
theorem _root_.solution {Λ t : ℕ} (ℓ : E →ₗ[K] K)
    (v : Fin t → Fin Λ → K) (target : Fin t → K) :
    (menuEvent ℓ v target).card = ∑ x : E,
      (univ.filter fun y : E => jointMap ℓ (fun i => evalVector Λ x (v i)) y = target).card := by
  simp only [menuEvent, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  congr 1
  apply propext
  exact funext_iff.symm
end ThreeSum.TernaryOriginalRowMenu
