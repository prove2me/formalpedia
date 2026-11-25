-- Prove2me | solution 1 for PI.Dv.Tr.epsSum_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:41.349939+00:00
-- url     : https://prove2.me/submissions/56a034b5-ae58-4325-a017-a9e0acb901cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_PI_Dv_Tr_of_mul_epsSum

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
open Classical
namespace PI.Dv.Tr
theorem _root_.solution (P : Pair K G) : epsSum P * epsSum P = ((Fintype.card P.H : ℕ) : K) • epsSum P := by
  conv_lhs => arg 1; rw [epsSum]
  rw [Finset.sum_mul]
  simp_rw [smul_mul_assoc, of_mul_epsSum, smul_smul, Units.inv_mul, one_smul]
  rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
end PI.Dv.Tr
