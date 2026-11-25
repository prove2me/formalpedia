-- Prove2me | solution 1 for PI.ZW.differentiable_gammaFactor_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:43.979011+00:00
-- url     : https://prove2.me/submissions/ad2dbb0d-615c-4e57-ad36-3af4721c0bc1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s => (gammaFactor χ s)⁻¹) := by
  by_cases h : χ.Even
  · simp only [DirichletCharacter.gammaFactor, h, if_true]
    exact Complex.differentiable_Gammaℝ_inv
  · simp only [DirichletCharacter.gammaFactor, h, if_false]
    exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)
end PI.ZW
