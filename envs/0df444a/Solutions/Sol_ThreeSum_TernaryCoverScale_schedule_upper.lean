-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.schedule_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:43.569293+00:00
-- url     : https://prove2.me/submissions/13a9cee2-2fdc-45f4-8cd4-34720eee6066

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_prime_crude_upper
import Theorems.Thm_ThreeSum_TernaryCoverScale_log2_le_of_le_pow
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
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
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency
namespace ThreeSum.TernaryCoverScale
theorem _root_.solution (m : ℕ) :
    frequencyFactor m*(Nat.log2 (prime m^2)+1) ≤ 2^234*(m+1)^7 := by
  have hL : fixedLength m+1 ≤ 2^27*(m+1) := by simp [fixedLength]; norm_num; omega
  have hD : TernaryPartitionCount.partitionLoss (7930225*m) (978268*m) ≤
      (fixedLength m+1)^3 := by
    unfold TernaryPartitionCount.partitionLoss fixedLength
    have h1 : 2*(7930225*m)+1 ≤ 100000000*m+1 := by omega
    have h2 : 3*(978268*m)+1 ≤ 100000000*m+1 := by omega
    have h3 : 2*(978268*m)+1 ≤ 100000000*m+1 := by omega
    simpa only [pow_succ, pow_zero, one_mul] using Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hF : frequencyFactor m ≤ 2^42*(fixedLength m+1)^6 := by
    have h3 : (3 : ℕ)^16 ≤ 2^32 := by norm_num
    have hs := Nat.pow_le_pow_left hD 2
    unfold frequencyFactor
    calc
      _ ≤ 4*2^32*(16*(fixedLength m+1)^3)^2 := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 h3) (Nat.pow_le_pow_left (Nat.mul_le_mul_left 16 hD) 2)
      _ = _ := by rw [mul_pow, ← pow_mul]; norm_num; ring
  have hp2 : prime m^2 ≤ 2^(4*fixedLength m+4) := by
    have h := Nat.pow_le_pow_left (prime_crude_upper m) 2
    simpa only [← pow_mul, show (2*fixedLength m+2)*2 = 4*fixedLength m+4 by omega] using h
  have hl := log2_le_of_le_pow hp2
  have ht : Nat.log2 (prime m^2)+1 ≤ 8*(fixedLength m+1) := by omega
  calc
    _ ≤ (2^42*(fixedLength m+1)^6)*(8*(fixedLength m+1)) := Nat.mul_le_mul hF ht
    _ = 2^45*(fixedLength m+1)^7 := by norm_num; ring
    _ ≤ 2^45*(2^27*(m+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 7)
    _ = _ := by rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
end ThreeSum.TernaryCoverScale
