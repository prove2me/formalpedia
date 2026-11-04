-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverScale.selected_scale_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:34:57.959643+00:00
-- url     : https://prove2.me/submissions/c8d39edf-2c60-4596-a80c-bbf48b3be4d7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_partition_le_prime
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_capExponent_mul_upper
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_polynomial_schedule_upper
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_wordList_sum
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedAddresses_codes_length
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_mem_bank
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_cost
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_wordList_length
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_one
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_two
import Theorems.Thm_ThreeSum_WeightedEnumeration_digitCost_zero
import Theorems.Thm_ThreeSum_WeightedEnumeration_mem_digits
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_bank
import Theorems.Thm_ThreeSum_WeightedGlobalBank_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_mem_nearWords
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_codes_length
import Theorems.Thm_ThreeSum_WeightedNearEnumeration_mem_digits
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_length
attribute [local simp] ThreeSum.TernaryBankEnumeration.wordList_sum
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryNearEnumeration.codes_length
attribute [local simp] ThreeSum.TernaryNearEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedAddresses.codes_length
attribute [local simp] ThreeSum.WeightedBankEnumeration.mem_bank
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_cost
attribute [local simp] ThreeSum.WeightedBankEnumeration.wordList_length
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_one
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_two
attribute [local simp] ThreeSum.WeightedEnumeration.digitCost_zero
attribute [local simp] ThreeSum.WeightedEnumeration.mem_digits
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_bank
attribute [local simp] ThreeSum.WeightedGlobalBank.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearBankEnumeration.mem_nearWords
attribute [local simp] ThreeSum.WeightedNearEnumeration.codes_length
attribute [local simp] ThreeSum.WeightedNearEnumeration.mem_digits



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency
namespace ThreeSum.WeightedGlobalCoverScale
theorem _root_.solution (C c d : ℕ) (hC : 0 < C) :
    ((c*(fixedLength (scale C c d)+1)^d)*
      (frequencyFactor (scale C c d)*(Nat.log2 (prime (scale C c d)^2)+1))*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C))^C ≤ prime (scale C c d) := by
  let k := momentOrder C
  let t := scaleAux C c d
  let m := scale C c d
  let A := 46*d+367
  let D := 2*d+15
  have hk : 0 < k := by dsimp [k, momentOrder]; positivity
  have hkt : C*k*A ≤ t := by dsimp [t,scaleAux,A,k]; ring_nf; omega
  have hdt : C*k*D ≤ t := by dsimp [t,scaleAux,D,k]; ring_nf; omega
  have hbt : C*(8*k^2+k+26) ≤ t := by dsimp [t,scaleAux,k]; omega
  have hc : c ≤ t := by dsimp [t,scaleAux]; omega
  have ht : 2 ≤ t := by dsimp [t,scaleAux]; omega
  have hm : 2*t^2+1 ≤ m := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  have hbudget := capExponent_mul_upper m k
  have hsmall : C*k*(A+D*t)+C*(8*k^2+k+26) ≤ m := by
    have hh := Nat.mul_le_mul_right t hdt
    nlinarith
  have hbig : C*k*(A+D*t)+C*(12*fixedLength m+8*k^2+26+k) ≤ k*(fixedPi m 1) := by
    have hmain : 12*C*fixedLength m+m ≤ k*(fixedPi m 1) := by
      dsimp [k,momentOrder,fixedLength,fixedPi]
      nlinarith
    nlinarith
  have hexp : C*(A+D*t+capExponent (prime m) (sourceCap m (prime m)) k) ≤ fixedPi m 1 := by
    have hh := Nat.mul_le_mul_left C hbudget
    have hx : k*(C*(A+D*t+capExponent (prime m) (sourceCap m (prime m)) k)) ≤ k*(fixedPi m 1) := by nlinarith
    exact Nat.le_of_mul_le_mul_left hx hk
  have hp := polynomial_schedule_upper c d t hc
  have hall := Nat.pow_le_pow_left (Nat.mul_le_mul_right
    (rawThreshold (prime m) (sourceCap m (prime m)) k) hp) C
  change _ ≤ prime m
  calc
    _ ≤ (2^(A+D*t)*rawThreshold (prime m) (sourceCap m (prime m)) k)^C := hall
    _ = 2^((A+D*t+capExponent (prime m) (sourceCap m (prime m)) k)*C) := by
      rw [rawThreshold, ← pow_add, ← pow_mul]
    _ ≤ 2^(fixedPi m 1) := Nat.pow_le_pow_right (by decide) (by simpa [Nat.mul_comm] using hexp)
    _ ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by
      simpa using Nat.mul_le_mul_left (2^(fixedPi m 1)) (Nat.one_le_pow (fixedPi m 2) 3 (by decide))
    _ ≤ prime m := partition_le_prime m
end ThreeSum.WeightedGlobalCoverScale
