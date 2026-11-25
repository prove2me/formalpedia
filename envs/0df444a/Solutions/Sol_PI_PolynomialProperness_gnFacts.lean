-- Prove2me | solution 1 for PI.PolynomialProperness.gnFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:07:26.996183+00:00
-- url     : https://prove2.me/submissions/0163bedc-0975-477f-b15d-3fd4bbf1caac

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Theorems.Thm_PI_PolynomialProperness_nsq_mulVec_le
import Theorems.Thm_PI_PolynomialProperness_gN_sq_cols
import Theorems.Thm_PI_PolynomialProperness_GN_gN_mul_le
import Theorems.Thm_PI_PolynomialProperness_GN_gN_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution : GNFacts := fun _ _ =>
  ⟨GN.gN_nonneg, GN.gN_mul_le, nsq_mulVec_le, gN_sq_cols⟩
end PI.PolynomialProperness
