-- Prove2me | solution 1 for PI.HookLower.diagHom_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:12.766386+00:00
-- url     : https://prove2.me/submissions/11029b94-1ed7-46ff-88c0-eb1726251b1a

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_diagHom_lpMinor

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
theorem _root_.solution {N : ℕ} (ν : Fin N → ℕ) :
    diagHom N (hw ℚ le_rfl ν) = monomial (M0 ν) 1 := by
  classical
  rw [hw, map_prod, M0, monomial_sum_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, diagHom_lpMinor, monomial_pow, one_pow]
end PI.HookLower
