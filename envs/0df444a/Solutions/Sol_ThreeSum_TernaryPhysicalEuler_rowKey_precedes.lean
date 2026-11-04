-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.rowKey_precedes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:03:16.548976+00:00
-- url     : https://prove2.me/submissions/906d854a-b42d-4d42-a788-d5180bfa8f1b

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_ordinal_spec
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_zero
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_bank
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_near
import Theorems.Thm_ThreeSum_TernaryPhysicalEuler_near_predecessor_present
import Theorems.Thm_ThreeSum_TernaryEuler_predecessor_rank_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv ∨
      ∃ j<nn, rowKey R bankWords nearWords nb nn T bv nv i.val=nv+j ∧
        rank (nearWords j)<rank R := by
  by_cases hz : (R i).val=0
  · rw [rowKey_zero R bankWords nearWords i hz]
    exact Or.inl (by omega)
  · have hp : 0<(R i).val := by omega
    by_cases hr : rank (predecessor R i)≤T
    · rw [rowKey_bank R bankWords nearWords i hp hr]
      have hh := (ordinal_spec (hbank _ hr)).1
      exact Or.inl (by omega)
    · have hh := ordinal_spec (near_predecessor_present Q R nearWords hnear hRQ i (by omega))
      refine Or.inr ⟨_,hh.1,rowKey_near R bankWords nearWords i hp (by omega),?_⟩
      rw [hh.2]
      exact predecessor_rank_lt R i hp
end ThreeSum.TernaryPhysicalEuler
