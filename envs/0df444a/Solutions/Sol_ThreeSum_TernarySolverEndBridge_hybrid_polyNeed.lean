-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.hybrid_polyNeed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:40.889891+00:00
-- url     : https://prove2.me/submissions/c58df749-acf1-46c2-8cf0-cd653aea4fef

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Definitions.Def_WeightedCache3SUM_Alias_6a1084014ed2fa0e
import Theorems.Thm_ThreeSum_TernaryHybridResources_poly_need


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {need : ℕ→ ℕ→ Need} (hp : PolyNeed need) (κ cutoff : ℕ) :
    PolyNeed (TernaryHybridResources.need need κ cutoff) :=
  TernaryHybridResources.poly_need need hp κ cutoff
end ThreeSum.TernarySolverEndBridge
