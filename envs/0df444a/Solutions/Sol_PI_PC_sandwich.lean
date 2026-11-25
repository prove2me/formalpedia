-- Prove2me | solution 1 for PI.PC.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:08.088869+00:00
-- url     : https://prove2.me/submissions/eaaf392d-2fbf-41bd-a7f0-7babc62b210f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Theorems.Thm_PI_PC_chD_le_psi
import Theorems.Thm_PI_PC_psi_sub_psi_le_chD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
namespace PI.PC
theorem _root_.solution : Sandwich := fun x _ => ⟨psi_sub_psi_le_chD x, chD_le_psi x⟩
end PI.PC
