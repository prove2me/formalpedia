-- Prove2me | solution 1 for PI.Dv.Tr.eps_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:12.951816+00:00
-- url     : https://prove2.me/submissions/da0ae87f-b9bf-44a8-b7a9-56ec18055d57

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_KudlaSiegelWeil
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Theorems.Thm_PI_Dv_Tr_eps_eq
import Theorems.Thm_PI_Dv_Tr_epsSum_sq

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
theorem _root_.solution (P : Pair K G) : eps P * eps P = eps P := by
  have hc : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eps_eq, smul_mul_smul_comm, epsSum_sq, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
end PI.Dv.Tr
