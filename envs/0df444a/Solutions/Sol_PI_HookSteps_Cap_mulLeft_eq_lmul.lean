-- Prove2me | solution 1 for PI.HookSteps.Cap.mulLeft_eq_lmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:33.849257+00:00
-- url     : https://prove2.me/submissions/d276f682-b41a-4f51-8168-b10ef3d7e8d5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset
namespace PI.HookSteps.Cap
theorem _root_.solution (N : ℕ) (p : MvPolynomial (Fin N × Fin N) ℚ) :
    LinearMap.mulLeft ℚ p = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) p := rfl
end PI.HookSteps.Cap
