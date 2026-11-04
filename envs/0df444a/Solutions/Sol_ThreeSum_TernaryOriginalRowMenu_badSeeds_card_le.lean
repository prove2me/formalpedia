-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.badSeeds_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:16.360514+00:00
-- url     : https://prove2.me/submissions/b18d2bf0-0799-4dbe-bea6-9cc077791184

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_vectorPoly_natDegree_le
import Theorems.Thm_ThreeSum_TernaryOriginalRowMenu_combination_ne_zero
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
theorem _root_.solution {Λ t : ℕ} (v : Fin t → Fin Λ → K)
    (hv : LinearIndependent K v) :
    (badSeeds (E := E) v).card ≤ (Fintype.card K ^ t - 1) * (Λ - 1) := by
  have hroot (c : Fin t → K) (hc : c ∈ univ.erase 0) :
      (univ.filter fun x => (combination (E := E) v c).eval x = 0).card ≤ Λ - 1 := by
    have hn := combination_ne_zero (E := E) v hv c (mem_erase.mp hc).1
    have hh : (univ.filter fun x => (combination (E := E) v c).eval x = 0).val ⊆
        (combination (E := E) v c).roots := by
      intro x hx
      exact (Polynomial.mem_roots hn).mpr (mem_filter.mp hx).2
    exact (Polynomial.card_le_degree_of_subset_roots hh).trans
      (vectorPoly_natDegree_le Λ _)
  calc
    _ ≤ ∑ c ∈ univ.erase (0 : Fin t → K),
        (univ.filter fun x => (combination (E := E) v c).eval x = 0).card :=
      card_biUnion_le
    _ ≤ ∑ _c ∈ univ.erase (0 : Fin t → K), (Λ - 1) := sum_le_sum hroot
    _ = _ := by simp
end ThreeSum.TernaryOriginalRowMenu
