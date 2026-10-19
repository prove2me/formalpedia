-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPermanentJacobian_eq_cross_selected_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/e639b971-4f3e-4079-9169-ad6619c6aa46

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermutationOutsideFactor_internal_product_zero
import Theorems.Thm_PermanentFormulaLowerBound_matchingPermanentJacobian_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {ell m : ℕ} (p q : Fin m → ℂ)
    (de ab : Fin m × Fin m) :
    matchingPermanentJacobian (ell := ell) p q de ab =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        ∏ i : {i : Fin ((ell + ell) + m) //
          i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
          MvPolynomial.eval (matchingPermanentSpecialization p q)
            (matchingPermutationOutsideFactor
              (matchingDiagonalEmbedding ell m) σ.1.1 i.1) := by
  classical
  let w (σ : Equiv.Perm (Fin ((ell + ell) + m))) : ℂ :=
    ∏ i : {i : Fin ((ell + ell) + m) //
      i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
      MvPolynomial.eval (matchingPermanentSpecialization p q)
        (matchingPermutationOutsideFactor
          (matchingDiagonalEmbedding ell m) σ i.1)
  have hselected :
      matchingPermanentJacobian (ell := ell) p q de ab =
        ∑ σ : MatchingBitSelectedPermutation ell m de ab, w σ.1 := by
    rw [matchingPermanentJacobian_apply]
    change
      (∑ σ : Equiv.Perm (Fin ((ell + ell) + m)),
        if matchingPermutationExponent
            (matchingDiagonalEmbedding ell m) σ =
              matchingSquarefreeMonomial
                (matchingBitCoefficientSet ell m de) ∧
            σ (matchingExternalEntry ell m ab.1 ab.2).1.1 =
              (matchingExternalEntry ell m ab.1 ab.2).1.2 then
          w σ
        else 0) =
        ∑ σ : MatchingBitSelectedPermutation ell m de ab, w σ.1
    rw [← Finset.sum_filter]
    apply Finset.sum_subtype
    intro σ
    simp
  have hvanish
      (σ : MatchingBitSelectedPermutation ell m de ab)
      (hnot : ¬ ∀ y : {y : Fin ell ⊕ Fin ell //
        y ∉ matchingBitCoefficientSet ell m de},
        ∃ j : Fin m,
          σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
            matchingBlockIndexEquiv ell m (.inr j)) :
      w σ.1 = 0 := by
    by_contra hnonzero
    apply hnot
    intro y
    cases himage :
      (matchingBlockIndexEquiv ell m).symm
        (σ.1 (matchingBlockIndexEquiv ell m (.inl y.1))) with
    | inl y' =>
        have hσ :
            σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
              matchingBlockIndexEquiv ell m (.inl y') := by
          have h := congrArg (matchingBlockIndexEquiv ell m) himage
          simpa only [Equiv.apply_symm_apply] using h
        have hne : y' ≠ y.1 := by
          intro heq
          subst y'
          have hfix :=
            (matchingPermutationExponent_eq_squarefree_iff
              (matchingDiagonalEmbedding ell m) σ.1
              (matchingBitCoefficientSet ell m de)).mp
                σ.property.1 y.1
          exact y.property (hfix.mp hσ)
        have hz :=
          matchingPermutationOutsideFactor_internal_product_zero
            p q σ.1 ab.1 ab.2 y.1 y' hne hσ
        exact (hnonzero hz).elim
    | inr j =>
        refine ⟨j, ?_⟩
        have h := congrArg (matchingBlockIndexEquiv ell m) himage
        simpa only [Equiv.apply_symm_apply] using h
  calc
    matchingPermanentJacobian (ell := ell) p q de ab =
        ∑ σ : MatchingBitSelectedPermutation ell m de ab, w σ.1 :=
      hselected
    _ =
        (∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
          w σ.1.1) +
        ∑ σ : {σ : MatchingBitSelectedPermutation ell m de ab //
          ¬ ∀ y : {y : Fin ell ⊕ Fin ell //
            y ∉ matchingBitCoefficientSet ell m de},
            ∃ j : Fin m,
              σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
                matchingBlockIndexEquiv ell m (.inr j)}, w σ.1.1 := by
      exact
        (Fintype.sum_subtype_add_sum_subtype
          (fun σ : MatchingBitSelectedPermutation ell m de ab =>
            ∀ y : {y : Fin ell ⊕ Fin ell //
              y ∉ matchingBitCoefficientSet ell m de},
              ∃ j : Fin m,
                σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
                  matchingBlockIndexEquiv ell m (.inr j))
          (fun σ => w σ.1)).symm
    _ = ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
          w σ.1.1 := by
      have hz :
          (∑ σ : {σ : MatchingBitSelectedPermutation ell m de ab //
            ¬ ∀ y : {y : Fin ell ⊕ Fin ell //
              y ∉ matchingBitCoefficientSet ell m de},
              ∃ j : Fin m,
                σ.1 (matchingBlockIndexEquiv ell m (.inl y.1)) =
                  matchingBlockIndexEquiv ell m (.inr j)},
            w σ.1.1) = 0 := by
        apply Finset.sum_eq_zero
        intro σ _
        exact hvanish σ.1 σ.property
      rw [hz, add_zero]
    _ =
      ∑ σ : MatchingBitCrossSelectedPermutation ell m de ab,
        ∏ i : {i : Fin ((ell + ell) + m) //
          i ≠ (matchingExternalEntry ell m ab.1 ab.2).1.1},
          MvPolynomial.eval (matchingPermanentSpecialization p q)
            (matchingPermutationOutsideFactor
              (matchingDiagonalEmbedding ell m) σ.1.1 i.1) := by
      rfl
end PermanentFormulaLowerBound
