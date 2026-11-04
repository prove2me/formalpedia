-- Prove2me | solution 1 for ThreeSum.ArithmeticStageBounds.arithmetic_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:15.893843+00:00
-- url     : https://prove2.me/submissions/f287c792-fe21-4bee-9d2b-3fddcecd3335

import Definitions.Def_Submission_ThreeSum_ModuloCosts
import Definitions.Def_Submission_ThreeSum_BudgetTime
import Definitions.Def_Submission_ThreeSum_ArithmeticStageBounds
import Definitions.Def_WeightedCache3SUM_Alias_d4d3bf606820e931
import Definitions.Def_WeightedCache3SUM_Alias_79670fd38525811b
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_pow
import Theorems.Thm_ThreeSum_StageBounds_concreteOverhead_powerBound


set_option autoImplicit false
open ThreeSum ThreeSum.ArithmeticStageBounds
open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology
set_option maxHeartbeats 1000000
noncomputable section
namespace ThreeSum.ArithmeticStageBounds
theorem _root_.solution (C k : ℕ) :
    PowerBound (arithmeticBudget C k)
      (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by
  have hm := (PowerBound.of_rate bandCount_log_rate).pow 2
  have hh := (concreteOverhead_powerBound C).mul
    (((PowerBound.const 3).mul hm).mul (perTriple_powerBound k))
  have heq : (0 : ℝ)+(0+2*(1-(E+bandShift)/5)+(8/5)*((E+1/2)/5)) =
      2+epsilon*(4/5-(2/5)*E-2*bandShift) := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  exact hh
end ThreeSum.ArithmeticStageBounds
