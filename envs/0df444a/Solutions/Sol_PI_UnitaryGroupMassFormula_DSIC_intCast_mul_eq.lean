-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DSIC.intCast_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:11.555971+00:00
-- url     : https://prove2.me/submissions/2532628f-160e-4666-8f4f-48e34b30c39d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_CentralScalar
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QuasiDeterminantConjInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open Finset
open scoped Matrix
namespace PI.UnitaryGroupMassFormula.DSIC
theorem _root_.solution {R : Type*} [Ring R] [Algebra ℂ R] (z : ℤ) (y : R) : (z : R) * y = (z : ℂ) • y := by
  rw [← zsmul_eq_mul, Int.cast_smul_eq_zsmul]
end PI.UnitaryGroupMassFormula.DSIC
