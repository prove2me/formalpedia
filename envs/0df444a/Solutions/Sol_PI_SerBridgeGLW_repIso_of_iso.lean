-- Prove2me | solution 1 for PI.SerBridgeGLW.repIso_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:16.80109+00:00
-- url     : https://prove2.me/submissions/19d176f2-0a6c-4352-8483-cb25c257a708

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_CharacterEqOfRepIso
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open PI PI.SerBridgeGLW
variable {G : Type} [Group G] [Fintype G]
namespace PI.SerBridgeGLW
theorem _root_.solution {V W : FDRep ℂ G} (i : V ≅ W) : RepIso V.ρ W.ρ := ⟨FDRep.isoToLinearEquiv i, fun γ v => by
    rw [FDRep.Iso.conj_ρ i γ]
    simp [LinearEquiv.conj_apply]⟩
end PI.SerBridgeGLW
