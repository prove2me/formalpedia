-- Prove2me | solution 1 for PI.ZW.gammaFactor_ne_zero_of_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:28.758059+00:00
-- url     : https://prove2.me/submissions/1b58e3da-4557-4c66-8f62-27295aa4b192

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
theorem _root_.solution {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  by_cases h : χ.Even
  · simp only [DirichletCharacter.gammaFactor, h, if_true]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · simp only [DirichletCharacter.gammaFactor, h, if_false]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
end PI.ZW
