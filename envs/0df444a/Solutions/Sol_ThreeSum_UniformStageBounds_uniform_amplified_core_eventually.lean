-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.uniform_amplified_core_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:07.387469+00:00
-- url     : https://prove2.me/submissions/14abd39b-0734-4a5a-b14e-425d7de5cb7f

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_workBudget_eventually_target
import Theorems.Thm_ThreeSum_UniformStageBounds_amplified_core_le_budget

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
    ∀ᶠ n : ℕ in atTop, ∀ W H P H1 : ℕ,
      W * radix n ≤ wantedNumerator n →
      P * H ≤ scoreLoss k n * H1 →
      H1 ≤ candidateCount n * rawTripleBound n →
      radix n ≤ primeLoss radix n * P →
      (amplifiedCoreWork C (fun _ => W) (fun _ => H) n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  filter_upwards [workBudget_eventually_target C k] with n hn
  intro W H P H1 hW hs hi hm
  have hb := amplified_core_le_budget (C := C) hW hs hi hm
  exact (show (amplifiedCoreWork C (fun _ => W) (fun _ => H) n : ℝ) ≤ workBudget C k n by
    exact_mod_cast hb).trans hn
end ThreeSum.UniformStageBounds
