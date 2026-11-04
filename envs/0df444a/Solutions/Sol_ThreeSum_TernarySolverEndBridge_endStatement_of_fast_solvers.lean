-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.endStatement_of_fast_solvers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:53.616347+00:00
-- url     : https://prove2.me/submissions/3d829673-6084-470f-a43e-97e27fa4da96

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_endStatement_of_solvers
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_solves
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_polyNeed
import Theorems.Thm_ThreeSum_TernarySolverEndBridge_hybrid_timeUpTo
import Theorems.Thm_ThreeSum_TernaryEndBridge_endStatement_of_solvers


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution
    (h : ∀ κ : ℕ,
      ∃ (P : Program) (p cutoff : ℕ) (T : ℕ→ ℕ) (need : ℕ→ ℕ→ Need) (a : ℝ),
        FastExecution P p κ cutoff T need ∧ PolyNeed need ∧
        PowerBound T a ∧ 0≤ a ∧ a<targetExponent) :
    EndStatement.ThreeSum.SolvedInTime (4800698571997281331/2500000000000000000:Rat) := by
  apply endStatement_of_solvers
  intro κ
  obtain ⟨P,p,cutoff,T,need,a,hexec,hp,ht,ha,hmargin⟩:= h κ
  exact ⟨TernaryHybridCore.program P p κ cutoff,P.length+5,
    TernaryHybridCore.time T κ cutoff,TernaryHybridResources.need need κ cutoff,
    hybrid_solves hexec,hybrid_polyNeed hp κ cutoff,hybrid_timeUpTo ht ha hmargin κ cutoff⟩
end ThreeSum.TernarySolverEndBridge
