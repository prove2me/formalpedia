-- Prove2me | solution 1 for PI.Dv.Tr.eps_mul_epsSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:57:14.180785+00:00
-- url     : https://prove2.me/submissions/5cc0aac6-8139-4e1d-992f-6c5fdc27a843

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_PI_Dv_Tr_epsSum_sq
import Theorems.Thm_PI_Dv_Tr_eps_eq


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
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
open Classical
namespace PI.Dv.Tr
theorem _root_.solution (P : Pair K G) : eps P * epsSum P = epsSum P := by
  have hc : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eps_eq, smul_mul_assoc, epsSum_sq, smul_smul, inv_mul_cancel₀ hc, one_smul]
end PI.Dv.Tr
