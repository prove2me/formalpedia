-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.hybrid_solvedAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:24:18.420722+00:00
-- url     : https://prove2.me/submissions/455ead8f-81de-4abc-8c5c-806311c5c3e0

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_solvedAt_of_solves
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_solves
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_polyNeed
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_timeUpTo
import Theorems.Thm_ThreeSum_TernaryEndBridge_solvedAt_of_solves


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {P : Program} {p κ cutoff : ℕ}
    {T : ℕ→ ℕ} {need : ℕ→ ℕ→ Need} {a : ℝ}
    (hexec : FastExecution P p κ cutoff T need) (hp : PolyNeed need)
    (ht : PowerBound T a) (ha : 0≤ a) (hmargin : a<targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (4800698571997281331/2500000000000000000:ℝ) 0 :=
  solvedAt_of_solves (hybrid_solves hexec) (hybrid_polyNeed hp κ cutoff)
    (hybrid_timeUpTo ht ha hmargin κ cutoff)
end ThreeSum.TernarySolverEndBridge
