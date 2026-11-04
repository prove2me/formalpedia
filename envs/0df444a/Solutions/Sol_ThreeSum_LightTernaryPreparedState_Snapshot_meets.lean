-- Prove2me | solution 1 for ThreeSum.LightTernaryPreparedState.Snapshot.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:49:11.093044+00:00
-- url     : https://prove2.me/submissions/aacd7696-5891-4609-8ef2-f2a3842e630d

import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_098d503c7eb426c7
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_meets
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_meets
import Theorems.Thm_ThreeSum_LightTernaryInversePass_meets
import Theorems.Thm_ThreeSum_LightTernaryMetadata_meets
import Theorems.Thm_ThreeSum_LightTernaryNearDigits_meets
import Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSourceWords_meets
import Theorems.Thm_ThreeSum_LightTernaryNearSource_meets
import Theorems.Thm_ThreeSum_LightTernaryPass_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_meets
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_meets
import Theorems.Thm_ThreeSum_LightTernaryProduct_meets
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_meets
import Theorems.Thm_ThreeSum_LightTernaryRankTable_meets
import Theorems.Thm_ThreeSum_LightTernaryRank_meets


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.LightTernaryPreparedWanted
set_option maxHeartbeats 6000000
namespace ThreeSum.LightTernaryPreparedState
namespace Snapshot
theorem _root_.solution {lim : Limits} {P : Program} {e : LightTernaryPreparedWanted.Entries} {pMain N out bankValues caps d : ℕ}
    (hmain : P[pMain]?=some (LightTernaryPreparedWanted.body e)) (lib : LightTernaryPreparedWanted.Library P e)
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (hd : d+3*N+f.L+13≤lim.depth) :
    Meets lim P pMain d (LightTernaryPreparedWanted.args out bankValues caps f g Q) μ (LightTernaryPreparedWanted.time f g Q)
      (fun v ν => v=stageValue N (LightTernaryWantedQuery.H F G) Q ∧ Kept μ ν f.a) := by
  exact LightTernaryPreparedWanted.meets hmain lib f g μ Q E F G
    S.fResources S.gResources S.outside S.ga S.gp S.gactive S.gbank S.gnb S.gT
    S.bankRead S.bankSorted S.Fbank S.Gbank S.bankBefore S.Fbefore S.Gbefore S.Hbefore S.Hbank
    S.dst S.caps S.active S.setupWord S.GRead S.FbeforeG S.Fout S.Gout S.outSpace S.outKeep
    S.productWord S.queryWord hd
end Snapshot
end ThreeSum.LightTernaryPreparedState
