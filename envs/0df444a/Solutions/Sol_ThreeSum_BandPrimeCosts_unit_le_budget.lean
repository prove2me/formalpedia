-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.unit_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:48.814674+00:00
-- url     : https://prove2.me/submissions/d4e20b07-22d2-45c4-9b5b-0a8ff487b2dc

import Definitions.Def_Submission_ThreeSum_LightBandPrimeSetup
import Definitions.Def_Submission_ThreeSum_BandPrimeScales
import Definitions.Def_Submission_ThreeSum_BandPrimeCosts
import Theorems.Thm_ThreeSum_ArithmeticStageBounds_invocation_le_budget
import Theorems.Thm_ThreeSum_KaratsubaInterface_le_capacity
import Theorems.Thm_ThreeSum_ModuloCosts_capacity_le_roundedPower


set_option autoImplicit false
open ThreeSum ThreeSum.BandPrimeCosts
open Scales BandScales CostLedger ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace ThreeSum.BandPrimeCosts
theorem _root_.solution {n : ℕ} (k : ℕ) (hn : 0 < n) :
    unit (maxMod n) (bandSize n) (n^k) ≤ 3*perTripleBudget k n := by
  have hc := invocation_le_budget (p := maxMod n) k hn le_rfl le_rfl le_rfl le_rfl
  have hp := (KaratsubaInterface.le_capacity (maxMod n)).trans (ModuloCosts.capacity_le_roundedPower (maxMod n))
  have hl : Nat.log 2 (maxMod n+1) ≤ maxMod n+1 := Nat.log_le_self _ _
  have hj : LightWeightedScore.jointTime (maxMod n) ≤ perTripleBudget k n := by
    unfold LightWeightedScore.jointTime LightResidues.residueBudget perTripleBudget
    omega
  have hlarge : 1000 ≤ perTripleBudget k n := by unfold perTripleBudget; omega
  unfold unit
  omega
end ThreeSum.BandPrimeCosts
