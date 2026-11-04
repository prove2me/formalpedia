-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.hybrid_timeUpTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:22.027895+00:00
-- url     : https://prove2.me/submissions/a9deb07a-3715-4156-99ec-27cbeeb8d87f

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryHybridCosts_timeUpTo_eventually


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {T : ℕ→ ℕ} {a : ℝ}
    (ht : PowerBound T a) (ha : 0≤ a) (hmargin : a<targetExponent) (κ cutoff : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      timeUpTo (TernaryHybridCore.time T κ cutoff) n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent :=
  TernaryHybridCosts.timeUpTo_eventually ht ha hmargin κ cutoff
end ThreeSum.TernarySolverEndBridge
