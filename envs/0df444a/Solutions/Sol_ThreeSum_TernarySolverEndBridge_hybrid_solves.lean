-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.hybrid_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:40.474196+00:00
-- url     : https://prove2.me/submissions/a74d7b2e-4815-489f-ba03-91cde6d66457

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryHybridCore_solves_of_fast


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {P : Program} {p κ cutoff : ℕ}
    {T : ℕ→ ℕ} {need : ℕ→ ℕ→ Need} (hexec : FastExecution P p κ cutoff T need) :
    Solves s3Task (TernaryHybridCore.program P p κ cutoff) (P.length+5)
      (TernaryHybridCore.time T κ cutoff) (TernaryHybridResources.need need κ cutoff) :=
  TernaryHybridCore.solves_of_fast need T hexec
end ThreeSum.TernarySolverEndBridge
