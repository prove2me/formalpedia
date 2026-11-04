-- Prove2me | solution 1 for ThreeSum.WeightedGlobalActualCleanupRuntime.prepared_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:39:57.495251+00:00
-- url     : https://prove2.me/submissions/8b8e47f7-2540-423f-9936-8eae99358dc3

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryPreparedPostSelection
import Definitions.Def_Submission_Weighted_Global_CountFrontendBudget
import Definitions.Def_Submission_Weighted_Global_TernaryActualCleanupRuntime
import Theorems.Thm_ThreeSum_WeightedGlobalActualCleanupRuntime_stage_bound
import Theorems.Thm_ThreeSum_LightOriginalCollisionScore_time_eq
import Theorems.Thm_ThreeSum_LightTernaryFinalPreparation_time_eq


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalActualCleanupRuntime
open Light WeightedGlobalLocalParameters
set_option maxHeartbeats 6000000
namespace ThreeSum.WeightedGlobalActualCleanupRuntime
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) (n : ℕ)
    (hA : c.nA≤n) (hB : c.nB≤n) (hC : c.nC≤n) :
    LightWeightedGlobalPreparedPostSelection.time S H c keysB keysC+673≤
      LightWeightedGlobalMomentReporter.time S H+
        10000*(c.L+1)*(n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1)) := by
  have hsb:=stage_bound keysB c.nB c.nA c.L n hB hA
  have hsc:=stage_bound keysC c.nC c.nA c.L n hC hA
  have hbase : 708*n+26*c.q+17*c.L+3972≤5000*(c.L+1)*(n+c.q+1) := by
    nlinarith [Nat.zero_le (c.L*n),Nat.zero_le (c.L*c.q)]
  have hinner : n*(120*c.L+330)+300≤1000*(c.L+1)*(n+1) := by
    nlinarith [Nat.zero_le (c.L*n)]
  have hbad:=Nat.mul_le_mul_left (collisions keysB c.nB+collisions keysC c.nC) hinner
  have hall : LightWeightedGlobalPreparedPostSelection.time S H c keysB keysC+673≤
      LightWeightedGlobalMomentReporter.time S H+708*n+26*c.q+17*c.L+3972+
        (collisions keysB c.nB+collisions keysC c.nC)*(n*(120*c.L+330)+300) := by
    unfold LightWeightedGlobalPreparedPostSelection.time LightTernaryFinalPreparation.time
      LightWeightedGlobalPostSelection.time LightOriginalSurvivorPair.time LightWeightedGlobalCompactReporter.time
    rw [LightOriginalCollisionScore.time_eq,LightOriginalCollisionScore.time_eq]
    unfold powTableTime
    nlinarith only [hsb,hsc,hB,hC]
  apply hall.trans
  have hrem :
      5000*(c.L+1)*(n+c.q+1)+
        (collisions keysB c.nB+collisions keysC c.nC)*(1000*(c.L+1)*(n+1))≤
      10000*(c.L+1)*(n+c.q+1+(collisions keysB c.nB+collisions keysC c.nC)*(n+1)) := by
    nlinarith [Nat.zero_le ((c.L+1)*(n+c.q+1)),
      Nat.zero_le ((c.L+1)*(collisions keysB c.nB+collisions keysC c.nC)*(n+1))]
  nlinarith only [hbase,hbad,hrem]
end ThreeSum.WeightedGlobalActualCleanupRuntime
