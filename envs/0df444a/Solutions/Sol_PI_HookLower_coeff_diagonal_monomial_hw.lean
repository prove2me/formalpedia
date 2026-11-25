-- Prove2me | solution 1 for PI.HookLower.coeff_diagonal_monomial_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:24:58.661656+00:00
-- url     : https://prove2.me/submissions/78e3e871-0e82-4a5e-88d0-71563e7821cd

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_coeff_diagHom
import Theorems.Thm_PI_HookLower_diagHom_hw
import Theorems.Thm_PI_HookLower_isDiag_diagonal_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower
namespace PI.HookLower
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) : coeff (M0 ν) (hw ℚ le_rfl ν) = 1 := by
  rw [← coeff_diagHom _ _ (isDiag_diagonal_monomial ν), diagHom_hw, coeff_monomial, if_pos rfl]
end PI.HookLower
