-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.workBudget_eventually_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:15:56.335113+00:00
-- url     : https://prove2.me/submissions/d689f41f-0063-4b06-904c-b6f71f12a6f1

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_workBudget_powerBound
import Theorems.Thm_ThreeSum_Parameters_certificate_lt_target


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
theorem _root_.solution (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (workBudget C k n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  have hh := (workBudget_powerBound C k)
    (targetExponent - certificateExponent) (sub_pos.mpr certificate_lt_target)
  have hid : certificateExponent + (targetExponent - certificateExponent) = targetExponent := by ring
  rw [hid] at hh
  exact hh
end ThreeSum.UniformStageBounds
