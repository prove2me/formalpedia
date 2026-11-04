-- Prove2me | solution 1 for ThreeSum.TernaryCoverScale.radix_power_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:44.657051+00:00
-- url     : https://prove2.me/submissions/4ad170e9-e112-4d96-a93b-0d0519f821d7

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Theorems.Thm_ThreeSum_TernaryCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_TernaryCoverScale_prime_square_le_cube
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
theorem _root_.solution {m n : ℕ} (hm : 0 < m) (hn : 1 < n) :
    prime m^(radixLength m n) ≤ outputSize m^2*n^3 := by
  have hM : 1 < outputSize m := lt_of_lt_of_le (by decide : 1 < (16 : ℕ)) (outputSize_ge_sixteen hm)
  have hn2 : 1 < n^2 := by nlinarith
  have hpos := Nat.clog_pos hM hn2
  have hl := Nat.pow_pred_clog_lt_self hM hn2
  have hexp : outputSize m^(radixLength m n) ≤ outputSize m*n^2 := by
    have he : radixLength m n = (Nat.clog (outputSize m) (n^2)).pred+1 := by
      exact (Nat.succ_pred_eq_of_pos hpos).symm
    rw [he, pow_succ]
    exact (Nat.mul_le_mul_right (outputSize m) hl.le).trans_eq (Nat.mul_comm _ _)
  have hp := Nat.pow_le_pow_left (prime_square_le_cube hm) (radixLength m n)
  have hx := Nat.pow_le_pow_left hexp 3
  have hpow : (prime m^(radixLength m n))^2 ≤ (outputSize m^2*n^3)^2 := by
    calc
      _ ≤ (outputSize m^(radixLength m n))^3 := by
        simpa only [← pow_mul, Nat.mul_comm] using hp
      _ ≤ (outputSize m*n^2)^3 := hx
      _ ≤ (outputSize m^2*n^3)^2 := by
        have h1 : 1 ≤ outputSize m := hM.le
        have hh := Nat.mul_le_mul_right ((outputSize m)^3*n^6) h1
        convert hh using 1 <;> ring
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hpow
end ThreeSum.TernaryCoverScale
