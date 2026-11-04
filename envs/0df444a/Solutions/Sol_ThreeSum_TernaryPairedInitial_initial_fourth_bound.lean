-- Prove2me | solution 1 for ThreeSum.TernaryPairedInitial.initial_fourth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:01.63023+00:00
-- url     : https://prove2.me/submissions/91a85370-8e23-424b-93de-b96348f543e4

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_original_bound
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
open ThreeSum ThreeSum.TernaryPairedInitial
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
namespace ThreeSum.TernaryPairedInitial
theorem _root_.solution {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b n carries C : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b)
    (hG : Fintype.card G≤n*carries) (hP : Fintype.card P≤n^2)
    (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e))^4 ≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by
  have hh := Nat.pow_le_pow_left (initial_original_bound K Λ b n carries A hA hG hP) 4
  have h := Nat.mul_le_mul_left (n^(8*K+4)*((2*K).factorial*b^(2*K))^8) hcarry
  calc
    _ ≤ (n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2)^4 := hh
    _ = (n^(8*K+4)*((2*K).factorial*b^(2*K))^8)*(carries^4*Λ^(8*K)) := by
      simp only [mul_pow,←pow_mul]
      have he : (2*K+1)*4=8*K+4 := by ring
      have he' : (2*K)*4=8*K := by ring
      rw [he,he']
      ring
    _ ≤ (n^(8*K+4)*((2*K).factorial*b^(2*K))^8)*(C*n) := h
    _ = _ := by rw [show 8*K+5=(8*K+4)+1 by omega,pow_succ]; ring
end ThreeSum.TernaryPairedInitial
