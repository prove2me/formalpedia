-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.budget_terminal_powerBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:19.328567+00:00
-- url     : https://prove2.me/submissions/01002201-e790-4ff5-81f9-353cf13012c4

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_falseBudget_powerBound
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_const
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_mul
import Theorems.Thm_ThreeSum_StageBounds_PowerBound_of_rate
import Definitions.Def_WeightedCache3SUM_Alias_7657fba77cd7b9c1
import Definitions.Def_WeightedCache3SUM_Alias_dc2f19a97a662b74


set_option autoImplicit false
open ThreeSum ThreeSum.UniformStageBounds
open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales ThreeSum.StageBounds
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.UniformStageBounds
theorem _root_.solution (k : ℕ) :
    PowerBound (terminalCount (falseBudget k))
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by
  have hh := (((PowerBound.const 2).mul (falseBudget_powerBound k)).mul
    (PowerBound.of_rate representationBound_log_rate)).mul (PowerBound.of_rate terminalChoices_log_rate)
  have heq : ((0 : ℝ) + (2 - (1 / 2 - bandShift) / 5) + kappa / 5) +
      (1 - terminalFraction) / 5 =
      2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh
end ThreeSum.UniformStageBounds
