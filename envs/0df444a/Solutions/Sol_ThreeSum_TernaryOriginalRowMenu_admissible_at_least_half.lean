-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.admissible_at_least_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:15:09.873609+00:00
-- url     : https://prove2.me/submissions/574d3f30-67b0-4255-809f-283b81298845

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_menuEvent_nine_eighths
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_row_eq_dot
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_proper_span_annihilator
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
theorem _root_.solution (Λ : ℕ) (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤)
    (hp : 3 ≤ Fintype.card K)
    (hsize : 8*Λ*Fintype.card K ^ 2 ≤ Fintype.card E) :
    Fintype.card E ^ 2 ≤ 2*(admissible Λ ℓ V).card := by
  obtain ⟨v,hv,hann⟩ := proper_span_annihilator Λ V hV
  let bad := univ.filter fun seed : E × E => seedRow Λ ℓ seed ∈ V
  have hind : LinearIndependent K (fun _ : Fin 1 => v) := by
    simpa only [linearIndependent_unique_iff] using hv
  have hs := menuEvent_nine_eighths ℓ hℓ (fun _ : Fin 1 => v) hind 0
    (by simpa using hsize)
  have hsub : bad ⊆ menuEvent ℓ (fun _ : Fin 1 => v) 0 := by
    intro seed hseed
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    rw [row_eq_dot]
    exact hann _ (mem_filter.mp hseed).2
  have hb := Nat.mul_le_mul_left (8*Fintype.card K) (card_le_card hsub)
  simp only [pow_one] at hs
  have hpart : bad.card + (admissible Λ ℓ V).card = Fintype.card E ^ 2 := by
    have hh := card_filter_add_card_filter_not (s := (univ : Finset (E × E)))
      (p := fun seed => seedRow Λ ℓ seed ∈ V)
    simpa only [admissible, bad, card_univ, Fintype.card_prod, pow_two] using hh
  nlinarith
end ThreeSum.TernaryOriginalRowMenu
