-- Prove2me | solution 1 for PermanentFormulaLowerBound.RationalFormula.exists_contractedRationalSkeleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:12.090475+00:00
-- url     : https://prove2.me/submissions/a01af16d-0dc5-43d7-83e8-5089c59ed4a2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_RationalFormula_splitEval_ne_zero_of_eval_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
open PermanentFormulaLowerBound.RationalFormula
noncomputable section
variable {Y Z F : Type*}
namespace PermanentFormulaLowerBound.RationalFormula
theorem _root_.solution [Field F]
    (f : RationalFormula (Y ⊕ Z) F) :
    Valid f → 0 < yLeafCount f → Nonempty (ContractedRationalSkeleton f) := by
  induction f with
  | var i =>
      intro _ hmarked
      cases i with
      | inl i => exact ⟨contractedRationalSkeletonVar i⟩
      | inr i => simp [yLeafCount] at hmarked
  | const c =>
      intro _ hmarked
      simp [yLeafCount] at hmarked
  | add f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | add hfvalid hgvalid =>
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonAddRight wg hfzero⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonAddLeft wf hgzero⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonAddBinary wf wg hfpos hgpos⟩
  | sub f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | sub hfvalid hgvalid =>
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonSubRight wg hfzero⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonSubLeft wf hgzero⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonSubBinary wf wg hfpos hgpos⟩
  | mul f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | mul hfvalid hgvalid =>
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonMulRight wg hfzero⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonMulLeft wf hgzero⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonMulBinary wf wg hfpos hgpos⟩
  | div f g ihf ihg =>
      intro hvalid hmarked
      cases hvalid with
      | div hfvalid hgvalid hgden =>
          have hsplitden : splitEval g ≠ 0 :=
            splitEval_ne_zero_of_eval_ne_zero hgden
          by_cases hfzero : yLeafCount f = 0
          · have hgpos : 0 < yLeafCount g := by
              simp only [yLeafCount] at hmarked
              omega
            obtain ⟨wg⟩ := ihg hgvalid hgpos
            exact ⟨contractedRationalSkeletonDivRight wg hfzero hsplitden⟩
          · have hfpos : 0 < yLeafCount f := Nat.pos_of_ne_zero hfzero
            obtain ⟨wf⟩ := ihf hfvalid hfpos
            by_cases hgzero : yLeafCount g = 0
            · exact ⟨contractedRationalSkeletonDivLeft wf hgzero hsplitden⟩
            · have hgpos : 0 < yLeafCount g := Nat.pos_of_ne_zero hgzero
              obtain ⟨wg⟩ := ihg hgvalid hgpos
              exact ⟨contractedRationalSkeletonDivBinary wf wg hfpos hgpos⟩
end PermanentFormulaLowerBound.RationalFormula
