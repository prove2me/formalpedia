-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.realized_of_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:46.326197+00:00
-- url     : https://prove2.me/submissions/1059b742-def7-4708-99f2-1d15a2e13fe0

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_realized_of_solves


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {P : Program} {p : ℕ} {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need) :
    ThreeSumApsp.WordRam.Realized EndStatement.ThreeSum (timeUpTo T) :=
  TernaryEndBridge.realized_of_solves hs hp
end ThreeSum.TernarySolverEndBridge
