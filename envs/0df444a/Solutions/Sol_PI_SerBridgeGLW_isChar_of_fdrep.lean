-- Prove2me | solution 1 for PI.SerBridgeGLW.isChar_of_fdrep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:30.457079+00:00
-- url     : https://prove2.me/submissions/c18d1998-8842-4a2a-8656-38125be998fb

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
theorem _root_.solution (V : FDRep ℂ G) : IsChar V.character := by
  classical
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V,
    MonoidHom.toHomUnits ((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp V.ρ), fun x => ?_⟩
  simp [FDRep.character, LinearMap.trace_eq_matrix_trace ℂ b]
  rfl
end PI.SerBridgeGLW
