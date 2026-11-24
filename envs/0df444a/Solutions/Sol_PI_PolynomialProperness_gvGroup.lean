-- Prove2me | solution 1 for PI.PolynomialProperness.gvGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:15:38.173124+00:00
-- url     : https://prove2.me/submissions/9ee34bfc-f03d-4d7b-b45c-f7db0012158f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Theorems.Thm_PI_PolynomialProperness_GN_inv_eq
import Theorems.Thm_PI_PolynomialProperness_GN_inv_mem
import Theorems.Thm_PI_PolynomialProperness_GN_inv_mul
import Theorems.Thm_PI_PolynomialProperness_GN_mul_inv
import Theorems.Thm_PI_PolynomialProperness_GN_mul_mem


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
theorem _root_.solution : GVGroup := fun _ _ =>
  ⟨fun _ hg _ hh => GN.mul_mem hg hh,
    fun _ hg => ⟨GN.inv_eq hg, GN.inv_mem hg, GN.mul_inv hg, GN.inv_mul hg⟩⟩
end PI.PolynomialProperness
