-- Prove2me | solution 1 for ThreeSum.TernaryPairedInitial.initial_original_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:36.097196+00:00
-- url     : https://prove2.me/submissions/66cbdc60-5264-4ccc-bc79-5ba51eac686c

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
import Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_bound
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
    (K Λ b n carries : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b)
    (hG : Fintype.card G≤n*carries) (hP : Fintype.card P≤n^2) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e)) ≤
      n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
  have hh := initial_bound K Λ b A hA
  have hcounts := Nat.mul_le_mul hG (Nat.pow_le_pow_left hP K)
  have h := Nat.mul_le_mul_right (Λ^(2*K)*((2*K).factorial*b^(2*K))^2) hcounts
  have he : n*carries*(n^2)^K*(Λ^(2*K)*((2*K).factorial*b^(2*K))^2) =
      n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
    rw [←pow_mul,pow_add,pow_one]
    ring
  rw [he] at h
  exact hh.trans (by simpa only [mul_assoc] using h)
end ThreeSum.TernaryPairedInitial
