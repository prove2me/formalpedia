-- Prove2me | solution 1 for PI.SerBridgeGLW.conjugate_character_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:09.026942+00:00
-- url     : https://prove2.me/submissions/39f854f7-bd08-4ede-a480-d9302cf4d61e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_IrrCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Theorems.Thm_PI_SerBridgeGLW_trace_inv_of_monoidHom
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
open Matrix ComplexOrder
open PI PI.SerBridgeGLW
namespace PI.SerBridgeGLW
theorem _root_.solution : ConjChar := by
  intro G _ _ V x
  let b := Module.finBasis ℂ V
  let M : G →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp V.ρ
  have hc : ∀ y, V.character y = Matrix.trace (M y) := fun y => by
    simp only [FDRep.character, M, MonoidHom.comp_apply]
    rw [LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  rw [hc, hc]
  exact trace_inv_of_monoidHom M x
end PI.SerBridgeGLW
