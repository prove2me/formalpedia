-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.F.EigA.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:25.753118+00:00
-- url     : https://prove2.me/submissions/0090ccf9-7480-4d62-9939-74a02a363483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetOperatorsCommOfAntiInvolution
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_FixedSpaceRankOne_FinrankFixedEqOne
import Theorems.Thm_PositivityTheory_Rg_BcB_F_EigA_finiteIndex_stabK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.EigA
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.BcB.F.EigA
theorem _root_.solution {K : Subgroup G} (hK : GelPair K) (g : G) : Finite (K ⧸ stabK K g) := by
  haveI := finiteIndex_stabK (hK.1 g)
  infer_instance
end PositivityTheory.Rg.BcB.F.EigA
