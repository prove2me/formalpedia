-- Prove2me | solution 1 for PI.Dv.Tr.eS_eps_eS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:10.506732+00:00
-- url     : https://prove2.me/submissions/8998e652-ce55-4f3a-a97d-416419d5f8e2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFiniteOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Theorems.Thm_PI_Dv_Tr_eS_comm
import Theorems.Thm_PI_Dv_Tr_eS_idem
import Theorems.Thm_PI_Dv_Tr_eS_orth


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
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (P : Pair K G) (s t : T.S) :
    eS T t * (eps P * eS T s) = if s = t then eps P * eS T s else 0 := by
  rw [← mul_assoc, ← eS_comm, mul_assoc]
  split_ifs with h
  · subst h; rw [eS_idem]
  · rw [eS_orth T t s (Ne.symm h), mul_zero]
end PI.Dv.Tr
