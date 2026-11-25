-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Elem_cauchyBinet_b49b24ee53ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:50.770558+00:00
-- url     : https://prove2.me/submissions/09a7ccc2-dd44-4b6e-92ca-312952bdd277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Pluecker
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_injective_29260bc550f2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_subsetCols_mem_800373af329f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_exists_subsetCols_eq_c3757fb2533e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_mul_expand_87daf8b7a418
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Elem_det_submatrix_eq_zero_of_not_injective_54a2168de0b0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open Matrix Finset
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.Elem
variable {R : Type*} [CommRing R] {κ : Type*}
namespace GroundTheory.Heights₂.Heights.RestTerms.Elem
theorem _root_.solution [Fintype κ] [DecidableEq κ] {p : ℕ} (A : Matrix (Fin p) κ R) (B : Matrix κ (Fin p) R) :
    (A * B).det = ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det := by
  rw [det_mul_expand]
  rw [← Finset.sum_filter_of_ne (p := Function.Injective) (fun φ _ h => by
        by_contra hφ
        exact h (by rw [det_submatrix_eq_zero_of_not_injective A φ hφ, zero_mul]))]
  have hpairs : ∑ S : {s : Finset κ // s.card = p},
      (A.submatrix id (subsetCols S)).det * (B.submatrix (subsetCols S) id).det =
      ∑ x : {s : Finset κ // s.card = p} × Equiv.Perm (Fin p),
        (A.submatrix id (subsetCols x.1 ∘ x.2)).det * ∏ i, B (subsetCols x.1 (x.2 i)) i := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [det_apply' (B.submatrix _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    have : A.submatrix id (subsetCols S ∘ π) =
        (A.submatrix id (subsetCols S)).submatrix id π := rfl
    rw [this, det_permute']
    simp only [submatrix_apply, id]
    ring
  rw [hpairs]
  symm
  refine Finset.sum_bij (fun x _ => subsetCols x.1 ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (subsetCols_injective x.1).comp x.2.injective
  · rintro ⟨S, π⟩ _ ⟨T, π'⟩ _ hxy
    simp only at hxy
    have hST : S = T := by
      apply Subtype.ext
      ext k
      constructor
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq S hk
        have := congrFun hxy (π.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [this]
        exact subsetCols_mem T _
      · intro hk
        obtain ⟨i, rfl⟩ := exists_subsetCols_eq T hk
        have := congrFun hxy (π'.symm i)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
        rw [← this]
        exact subsetCols_mem S _
    subst hST
    have : π = π' := by
      ext i
      exact congrArg Fin.val (subsetCols_injective S (congrFun hxy i))
    rw [this]
  · intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    let S : {s : Finset κ // s.card = p} :=
      ⟨Finset.univ.image φ, by rw [Finset.card_image_of_injective _ hφ]; simp⟩
    let g : Fin p → Fin p := fun i =>
      S.1.equivFinOfCardEq S.2 ⟨φ i, Finset.mem_image_of_mem φ (Finset.mem_univ i)⟩
    have hg : Function.Injective g := by
      intro i j h
      have := (S.1.equivFinOfCardEq S.2).injective h
      exact hφ (congrArg Subtype.val this)
    refine ⟨(S, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg)),
      Finset.mem_univ _, ?_⟩
    funext i
    simp [subsetCols, g, S]
  · intro x _
    rfl
end GroundTheory.Heights₂.Heights.RestTerms.Elem
