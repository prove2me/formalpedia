-- Prove2me | solution 1 for ThreeSum.LightWeightedPreparedState.Snapshot.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:46:28.736893+00:00
-- url     : https://prove2.me/submissions/10959822-2383-4aa4-97ee-cf99ff47dbf4

import Definitions.Def_Submission_Weighted_PreparedWanted
import Definitions.Def_Submission_Weighted_PreparedState
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Theorems.Thm_ThreeSum_LightCacheEnumeration_meets
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_meets
import Theorems.Thm_ThreeSum_LightWeightedCost_meets
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightWeightedNearDigits_meets
import Theorems.Thm_ThreeSum_LightWeightedNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightWeightedNearSource_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_meets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
open ThreeSum.LightWeightedPreparedWanted
set_option maxHeartbeats 6000000
namespace ThreeSum.LightWeightedPreparedState
namespace Snapshot
theorem _root_.solution {lim : Limits} {P : Program} {e : LightWeightedPreparedWanted.Entries} {pMain N out bankValues caps d : ℕ}
    (hmain : P[pMain]?=some (LightWeightedPreparedWanted.body e)) (lib : LightWeightedPreparedWanted.Library P e)
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (hd : d+3*N+f.L+13≤lim.depth) :
    Meets lim P pMain d (LightWeightedPreparedWanted.args out bankValues caps f g Q) μ (LightWeightedPreparedWanted.time f g Q)
      (fun v ν => v=stageValue N (LightWeightedWantedQuery.H F G) Q ∧ Kept μ ν f.a) := by
  exact LightWeightedPreparedWanted.meets hmain lib f g μ Q E F G
    S.fResources S.gResources S.outside S.ga S.gp S.gactive S.gbank S.gnb S.gT
    S.bankRead S.bankSorted S.Fbank S.Gbank S.bankBefore S.Fbefore S.Gbefore S.Hbefore S.Hbank
    S.dst S.caps S.active S.setupWord S.GRead S.FbeforeG S.Fout S.Gout S.outSpace S.outKeep
    S.productWord S.queryWord hd
end Snapshot
end ThreeSum.LightWeightedPreparedState
