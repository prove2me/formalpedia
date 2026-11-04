-- Prove2me | solution 1 for ThreeSum.HierarchyScales.initial_upper_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:46:33.673533+00:00
-- url     : https://prove2.me/submissions/bbae016c-af4d-4795-a953-ef9b18337938

import Definitions.Def_Submission_ThreeSum_CostLedger
import Definitions.Def_Submission_ThreeSum_HierarchyScales

set_option autoImplicit false
open ThreeSum ThreeSum.HierarchyScales
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace ThreeSum.HierarchyScales
theorem _root_.solution {n : ℕ} (hmu : 50 ≤ mu n) :
    initialTheta + 1 / (mu n : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by
  have hm : (50 : ℝ) ≤ mu n := by exact_mod_cast hmu
  have hp : (0 : ℝ) < mu n := by linarith
  have hu : 1 / (mu n : ℝ) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) hm
  constructor
  · unfold initialTheta; positivity
  · unfold initialTheta; linarith
end ThreeSum.HierarchyScales
