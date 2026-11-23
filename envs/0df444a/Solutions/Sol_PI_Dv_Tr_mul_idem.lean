-- Prove2me | solution 1 for PI.Dv.Tr.mul_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:01.505902+00:00
-- url     : https://prove2.me/submissions/b0eb1aba-4541-407b-9ac9-770f7c7a89df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
namespace PI.Dv.Tr
theorem _root_.solution {R : Type*} [Semiring R] {a b : R} (ha : a * a = a) (hb : b * b = b) (hc : b * a = a * b) :
    (a * b) * (a * b) = a * b := by
  rw [mul_assoc, ← mul_assoc b, hc, mul_assoc, hb, ← mul_assoc, ha]
end PI.Dv.Tr
