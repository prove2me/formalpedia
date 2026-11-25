-- Prove2me | solution 1 for PI.PolynomialProperness.TM.pX_mX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:30.066611+00:00
-- url     : https://prove2.me/submissions/4eb22775-47eb-4168-a62c-d87d03f2fe04

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_eI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x : Fin (2 * r + k + 1) → ℂ) :
    pX k r (mX k r vX *ᵥ x) = vX *ᵥ pX k r x := by
  funext a
  exact mX_mulVec_eI k r vX x a
end PI.PolynomialProperness.TM
