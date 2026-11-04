-- Prove2me | solution 1 for ThreeSum.WeightedGlobalColoredLoopSetup.originals_query_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T02:19:35.732341+00:00
-- url     : https://prove2.me/submissions/7677c367-eaf8-476f-b317-9dc1653be92f

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Fintype E]
    [DecidableEq E] [Algebra (ZMod p) E] {I : Input} {A : Inputs}
    {seedCount featureBound tagBound positionCap : ℕ} {ell : E→ₗ[ZMod p] ZMod p}
    {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ : ℕ→ℤ}
    (H : WeightedGlobalArenaPrefixInputs.Originals I A seedCount featureBound tagBound positionCap ell seeds L R O μ)
    (t : ℕ) :
    WeightedGlobalArenaPrefixInputs.Originals {I with queryTime:=t} A seedCount featureBound tagBound positionCap ell seeds L R O μ := by
  exact ⟨H.BEnd,H.CEnd,H.OEnd,H.menuEnd,H.positionEnd,H.leftEnd,H.rightEnd,H.feature,
    H.BBound,H.CBound,H.OBound,H.leftBound,H.rightBound,H.BRead,H.CRead,H.ORead,
    H.menuRead,H.positionRead,H.positionBound,H.leftRead,H.rightRead⟩
end ThreeSum.WeightedGlobalColoredLoopSetup
