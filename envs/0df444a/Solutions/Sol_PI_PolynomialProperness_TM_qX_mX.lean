-- Prove2me | solution 1 for PI.PolynomialProperness.TM.qX_mX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:34:28.556261+00:00
-- url     : https://prove2.me/submissions/dfc8c44c-97f9-4d08-aa13-58f8c62886fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_esI

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
    qX k r (mX k r vX *ᵥ x) = (vXᴴ)⁻¹ *ᵥ qX k r x := by
  funext a
  exact mX_mulVec_esI k r vX x a
end PI.PolynomialProperness.TM
