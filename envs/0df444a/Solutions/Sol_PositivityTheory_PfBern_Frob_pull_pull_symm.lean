-- Prove2me | solution 1 for PositivityTheory.PfBern.Frob.pull_pull_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:42.7344+00:00
-- url     : https://prove2.me/submissions/5e6d6c04-8369-4dbd-bf3d-6a62f1383912

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_symm_apply
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply
attribute [local simp] PositivityTheory.PfBern.Frob.rtr_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_symm_apply
attribute [local simp] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply



set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.PfBern PositivityTheory.PfBern.Frob
namespace PositivityTheory.PfBern.Frob
theorem _root_.solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (F : SB Y) : pullHomeo e.symm (pullHomeo e F) = F :=
  Subtype.ext (funext fun y => by simp)
end PositivityTheory.PfBern.Frob
