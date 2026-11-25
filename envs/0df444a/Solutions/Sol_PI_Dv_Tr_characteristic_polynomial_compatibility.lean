-- Prove2me | solution 1 for PI.Dv.Tr.characteristic_polynomial_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:23.827347+00:00
-- url     : https://prove2.me/submissions/0d8825fc-9ba1-4046-a57b-39cf6433a507

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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (P : Pair K G) (y h : P.H) :
    ((P.chi y : Kˣ) : K) * (((P.chi (y * h))⁻¹ : Kˣ) : K) = (((P.chi h)⁻¹ : Kˣ) : K) := by
  rw [map_mul, mul_inv, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
end PI.Dv.Tr
