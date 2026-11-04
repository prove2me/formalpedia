-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.solvedAt_of_solves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:30.792187+00:00
-- url     : https://prove2.me/submissions/8f8b359f-91ed-4ad2-bc37-32880a83fe31

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernaryEndBridge_solvedAt_of_solves


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {κ : ℕ} {P : Program} {p : ℕ}
    {T : ℕ→ ℕ→ ℕ} {need : ℕ→ ℕ→ Need}
    (hs : Solves s3Task P p T need) (hp : PolyNeed need)
    (ht : ∀ᶠ n : ℕ in atTop,
      timeUpTo T n ((n:ℝ)^(κ:ℝ))≤ (n:ℝ)^targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (4800698571997281331/2500000000000000000:ℝ) 0 :=
  TernaryEndBridge.solvedAt_of_solves hs hp ht
end ThreeSum.TernarySolverEndBridge
