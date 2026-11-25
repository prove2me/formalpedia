-- Prove2me | solution 1 for PI.Dv.Tr.e_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:33.841988+00:00
-- url     : https://prove2.me/submissions/9e00c44d-3f2d-4d67-a8ee-42aa7ee942a1

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
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_MemRangeIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSLat
import Theorems.Thm_PI_Dv_Tr_eS_comm
import Theorems.Thm_PI_Dv_Tr_eS_idem


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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
namespace PI.Dv.Tr
theorem _root_.solution (Q : Pair K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps Q * eS T s))) :
    ρ.asAlgebraHom (eS T s) y = y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eS_comm, mul_assoc, eS_idem]
end PI.Dv.Tr
