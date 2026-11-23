-- Prove2me | solution 1 for PI.Dv.Tr.epsSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.709925+00:00
-- url     : https://prove2.me/submissions/5bfaabb8-2e74-44fe-a08e-c6d4f51e2851

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
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
theorem _root_.solution (P : Pair K G) : epsSum P = ((Fintype.card P.H : ℕ) : K) • eps P := by
  have hc : ((Fintype.card P.H : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [eps_eq, smul_smul, mul_inv_cancel₀ hc, one_smul]
end PI.Dv.Tr
