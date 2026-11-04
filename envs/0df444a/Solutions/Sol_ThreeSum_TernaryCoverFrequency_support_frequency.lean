-- Prove2me | solution 1 for ThreeSum.TernaryCoverFrequency.support_frequency
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:10.297185+00:00
-- url     : https://prove2.me/submissions/254e4969-3638-4922-831d-64a932bac482

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Definitions.Def_WeightedCache3SUM_Alias_20e0db851a3633f6
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverFrequency
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators
namespace ThreeSum.TernaryCoverFrequency
theorem _root_.solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℕ) (N p C a : ℕ) (hN : 0 < N)
    (hfirst : N * Fintype.card Ω ≤ 2*p^2*∑ w, f w)
    (hsecond : (∑ w, f w^2) ≤ C*Fintype.card Ω)
    (hscale : 4*p^4*C ≤ a*N^2) :
    Fintype.card Ω ≤ a * (univ.filter fun w => f w ≠ 0).card := by
  classical
  let g : Ω → ℝ := fun w => (f w : ℝ)
  have hW : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfirstR : (N : ℝ)*Fintype.card Ω ≤ 2*(p : ℝ)^2*∑ w, g w := by
    dsimp [g]
    exact_mod_cast hfirst
  have hsecondR : (∑ w, g w^2) ≤ (C : ℝ)*Fintype.card Ω := by
    dsimp [g]
    exact_mod_cast hsecond
  have hscaleR : 4*(p : ℝ)^4*C ≤ (a : ℝ)*(N : ℝ)^2 := by exact_mod_cast hscale
  have hG : (0 : ℝ) ≤ ∑ w, g w := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let supp := (univ.filter fun w => g w ≠ 0).card
  have hs : (∑ w, g w)^2 ≤ (supp : ℝ)*(∑ w, g w^2) := Cover.support_cauchy g
  have hsup : (0 : ℝ) ≤ supp := Nat.cast_nonneg _
  have hbound := mul_le_mul_of_nonneg_left hsecondR hsup
  have hsq : ((N : ℝ)*Fintype.card Ω)^2 ≤ 4*(p : ℝ)^4*(∑ w, g w)^2 := by
    have h := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)*Fintype.card Ω)
      (by positivity : (0 : ℝ) ≤ 2*(p : ℝ)^2*∑ w, g w)).mpr hfirstR
    have he : (2*(p : ℝ)^2*∑ w, g w)^2 = 4*(p : ℝ)^4*(∑ w, g w)^2 := by ring
    rw [he] at h
    exact h
  have hraw : (N : ℝ)^2*Fintype.card Ω ≤ 4*(p : ℝ)^4*C*(supp : ℝ) := by
    apply (mul_le_mul_iff_left₀ hW).mp
    have hc := mul_le_mul_of_nonneg_left (hs.trans hbound) (by positivity : (0 : ℝ) ≤ 4*(p : ℝ)^4)
    nlinarith
  have hfreq : (Fintype.card Ω : ℝ) ≤ (a : ℝ)*(supp : ℝ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hNr 2)).mp
    have hp := mul_le_mul_of_nonneg_right hscaleR hsup
    nlinarith
  have heq : (univ.filter fun w : Ω => g w ≠ 0) = (univ.filter fun w : Ω => f w ≠ 0) := by
    ext w
    simp [g]
  change (Fintype.card Ω : ℝ) ≤ (a : ℝ)*((univ.filter fun w => g w ≠ 0).card : ℝ) at hfreq
  rw [heq] at hfreq
  exact_mod_cast hfreq
end ThreeSum.TernaryCoverFrequency
