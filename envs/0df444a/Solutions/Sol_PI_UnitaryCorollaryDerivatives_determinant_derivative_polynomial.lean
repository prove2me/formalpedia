-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.determinant_derivative_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:59.055239+00:00
-- url     : https://prove2.me/submissions/c8bf23a0-54f8-457c-a7a8-906883cfd512

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_DjPoly
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_isPolyDeg_determinant_derivative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution : DjPoly := fun k j ρ => isPolyDeg_determinant_derivative k j ρ
end PI.UnitaryCorollaryDerivatives
