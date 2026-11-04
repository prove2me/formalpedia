-- Prove2me | solution 1 for ThreeSum.CostLedger.microOutputs_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:09:25.77261+00:00
-- url     : https://prove2.me/submissions/51d0f501-0148-4bd1-8293-58564e492911

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_BinomialEntropy_fixed_ratio_bounds
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_Switch_actual_totalSize
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
noncomputable section
namespace ThreeSum.CostLedger
theorem _root_.solution {n : ℕ} (hmu : 0 < mu n) :
    Real.log (microOutputs n : ℝ) ≤ 2 * E * muZero n * Real.log 2 := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hmR : (0 : ℝ) < muZero n := by exact_mod_cast hm
  have hb := (BinomialEntropy.fixed_ratio_bounds (c := 256) (r := 1)
    (by norm_num) (by norm_num) hm).2
  simp only [Nat.one_mul, Nat.cast_ofNat, Nat.cast_one] at hb
  have hc := (div_le_iff₀ hmR).mp hb
  change Real.log (((256 * muZero n).choose (muZero n) : ℕ) : ℝ) ≤ _
  have hid : 2 * E * (muZero n : ℝ) * Real.log 2 =
      256 * Real.binEntropy (1 / 256) * muZero n := by
    unfold E entropy
    field_simp
    <;> ring
  rw [hid]
  exact hc
end ThreeSum.CostLedger
