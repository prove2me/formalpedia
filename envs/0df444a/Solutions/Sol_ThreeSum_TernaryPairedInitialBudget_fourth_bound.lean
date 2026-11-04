-- Prove2me | solution 1 for ThreeSum.TernaryPairedInitialBudget.fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:08.507891+00:00
-- url     : https://prove2.me/submissions/7e3f0a8a-f09c-4335-86f4-4fec8ed5c110

import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitialBudget
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitialBudget
namespace ThreeSum.TernaryPairedInitialBudget
theorem _root_.solution (K Λ b n carries C : ℕ)
    (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (upper K Λ b n carries)^4≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by
  have h := Nat.mul_le_mul_left (n^(8*K+4)*((2*K).factorial*b^(2*K))^8) hcarry
  calc
    _ = (n^(8*K+4)*((2*K).factorial*b^(2*K))^8)*(carries^4*Λ^(8*K)) := by
      unfold upper
      simp only [mul_pow,←pow_mul]
      have h1 : (2*K+1)*4=8*K+4 := by omega
      have h2 : 2*K*4=8*K := by omega
      rw [h1,h2]
      ring
    _ ≤ _ := h
    _ = _ := by
      rw [show 8*K+5=(8*K+4)+1 by omega,pow_succ]
      ring
end ThreeSum.TernaryPairedInitialBudget
