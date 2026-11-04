-- Prove2me | solution 1 for ThreeSum.LightTernaryCountFrontend.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:12:06.217436+00:00
-- url     : https://prove2.me/submissions/afc4c995-7dc4-445a-b70e-2c621e15e64f

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRows
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_time_bound
import Theorems.Thm_ThreeSum_LightTernaryBankSweep_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_time_bound
import Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryNearSetup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryNearSource_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000
namespace ThreeSum.LightTernaryCountFrontend
theorem _root_.solution (groups N L n count t : ℕ) :
    time groups N L n count t≤40000*(groups+1)*(N+1)*(N+L+1)*(n+1)+(count+1)*(t+1000) := by
  have hb := LightTernaryGroupedBanks.time_bound groups N L n
  have hp : 1≤(groups+1)*(N+L+1)*(n+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_right (N+1) hp
  unfold time LightTernaryWantedRows.time LightTernaryWantedRowDispatch.time powTableTime
  nlinarith only [hb,hs]
end ThreeSum.LightTernaryCountFrontend
