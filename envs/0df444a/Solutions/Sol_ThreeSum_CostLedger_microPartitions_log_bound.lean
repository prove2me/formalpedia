-- Prove2me | solution 1 for ThreeSum.CostLedger.microPartitions_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:31.48377+00:00
-- url     : https://prove2.me/submissions/1d42aee1-ae05-4395-973e-edbaaba55536

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_CostLedger
import Theorems.Thm_ThreeSum_CostLedger_microPartitions_pos
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
theorem _root_.solution (n : ℕ) :
    Real.log (microPartitions n : ℝ) ≤ (muZero n : ℝ) * Real.log 2 := by
  have hp : (0 : ℝ) < microPartitions n := by exact_mod_cast microPartitions_pos n
  have hb : (microPartitions n : ℝ) ≤ (2 : ℝ) ^ muZero n := by
    exact_mod_cast Nat.choose_le_two_pow (muZero n) (muZero n / 2)
  simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hp hb
end ThreeSum.CostLedger
