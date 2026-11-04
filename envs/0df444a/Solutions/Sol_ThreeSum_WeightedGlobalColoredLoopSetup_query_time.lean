-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopSetup.query_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:11:33.32949+00:00
-- url     : https://prove2.me/submissions/fedda980-e0bd-418a-8891-b21fb4f7ccaf

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace ThreeSum.WeightedGlobalColoredLoopSetup
theorem _root_.solution (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (j : ℕ) (hj : j≤rounds P n) :
    WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j) (input P n free A B C)
      (valueCap (r:=j) P.maps P.cap (input P n free A B C))≤
      (input P n free A B C).queryTime := by
  change WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j) (baseInput P n free A B C)
      (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C))≤queryTime P n free A B C
  exact Finset.le_sup (f:=fun j => WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j)
    (baseInput P n free A B C) (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C)))
    (Finset.mem_range.mpr (by omega))
end ThreeSum.WeightedGlobalColoredLoopSetup
