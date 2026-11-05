-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup.query_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:04:36.3717+00:00
-- url     : https://prove2.me/submissions/894326ca-324e-43cb-ad57-ecbd191a18d8

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryColoredLoopSetup

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup
theorem _root_.solution (P : Profile κ) (n free : ℕ) (A B C : List ℤ) (j : ℕ) (hj : j≤rounds P n) :
    WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j) (input P n free A B C)
      (valueCap (r:=j) P.maps P.cap (input P n free A B C))≤
      (input P n free A B C).queryTime := by
  change WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j) (baseInput P n free A B C)
      (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C))≤queryTime P n free A B C
  exact Finset.le_sup (f:=fun j => WeightedGlobalArenaCountReady.queryTime (m:=P.m) (r:=j)
    (baseInput P n free A B C) (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C)))
    (Finset.mem_range.mpr (by omega))
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalColoredLoopSetup
