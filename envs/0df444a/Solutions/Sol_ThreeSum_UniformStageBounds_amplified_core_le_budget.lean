-- Prove2me | solution 1 for ThreeSum.UniformStageBounds.amplified_core_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:56:45.830915+00:00
-- url     : https://prove2.me/submissions/71cd0fa7-9b1f-4a16-bcf3-04a464e31479

import Definitions.Def_Submission_ThreeSum_StageBounds
import Definitions.Def_Submission_ThreeSum_UniformStageBounds
import Theorems.Thm_ThreeSum_UniformStageBounds_wanted_le_budget
import Theorems.Thm_ThreeSum_UniformStageBounds_false_le_budget
import Theorems.Thm_ThreeSum_UniformStageBounds_coreWork_mono

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
theorem _root_.solution {n C k W H P H1 : ℕ}
    (hW : W * radix n ≤ wantedNumerator n)
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    amplifiedCoreWork C (fun _ => W) (fun _ => H) n ≤ workBudget C k n := by
  have hm := coreWork_mono (n := n) (W := fun _ => W) (W' := wantedBudget)
    (H := fun _ => H) (H' := falseBudget k)
    (wanted_le_budget hW) (false_le_budget hscore hinit hmod)
  exact Nat.mul_le_mul_left (concreteOverhead C n) hm
end ThreeSum.UniformStageBounds
