-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.solvedAt_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:15.530273+00:00
-- url     : https://prove2.me/submissions/213792f4-ef9f-4e76-b843-b89fc263e74d

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_solvedAt_of_solves
import Theorems.Thm_ThreeSum_TernaryEndBridge_solvedAt_of_solves
import Theorems.Thm_ThreeSum_TernaryEndBridge_timeUpTo_eventually_of_uniform


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
    (ht : ∀ᶠ n : ℕ in atTop, ∀ U : ℕ, U≤ n^κ→ (T n U:ℝ)≤ (n:ℝ)^targetExponent) :
    ThreeSumApsp.WordRam.SolvedInTimeAt EndStatement.ThreeSum κ (4800698571997281331/2500000000000000000:ℝ) 0 :=
  solvedAt_of_solves hs hp (TernaryEndBridge.timeUpTo_eventually_of_uniform ht)
end ThreeSum.TernarySolverEndBridge
