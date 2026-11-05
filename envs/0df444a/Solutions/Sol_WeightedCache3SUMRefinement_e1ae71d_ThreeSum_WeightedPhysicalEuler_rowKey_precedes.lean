-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.rowKey_precedes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:23:06.282784+00:00
-- url     : https://prove2.me/submissions/8e9f996c-250e-4f21-a4d4-f252cde6e5a1

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_ordinal_spec
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_rowKey_zero
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_rowKey_bank
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_rowKey_near
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_near_predecessor_present
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_rank_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_WeightedCache_predecessor_rank_lt


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
theorem _root_.solution {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv ∨
      ∃ j<nn, rowKey R bankWords nearWords nb nn T bv nv i.val=nv+j ∧
        rank (nearWords j)<rank R := by
  by_cases hz : (R i).val=0
  · rw [rowKey_zero R bankWords nearWords i hz]
    exact Or.inl (by omega)
  · have hp : 0<(R i).val := by omega
    by_cases hr : cacheCost (predecessor R i)≤T
    · rw [rowKey_bank R bankWords nearWords i hp hr]
      have hh := (ordinal_spec (hbank _ hr)).1
      exact Or.inl (by omega)
    · have hh := ordinal_spec (near_predecessor_present Q R nearWords hnear hRQ i (by omega))
      refine Or.inr ⟨_,hh.1,rowKey_near R bankWords nearWords i hp (by omega),?_⟩
      rw [hh.2]
      exact predecessor_rank_lt R i hp
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
