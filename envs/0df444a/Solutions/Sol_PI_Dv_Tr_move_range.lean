-- Prove2me | solution 1 for PI.Dv.Tr.move_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:22.548825+00:00
-- url     : https://prove2.me/submissions/b91cb79e-f622-4bce-940c-e200b2b96849

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
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_Tr_eS_comm
import Theorems.Thm_PI_Dv_Tr_eps_idem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
namespace PI.Dv.Tr
theorem _root_.solution (Q _Q' : Pair K G) (g : G) (y : V) (hy : ρ.asAlgebraHom (eS T s) y = y) :
    ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y ∈ LinearMap.range (ρ.asAlgebraHom (eps Q * eS T s)) := by
  refine ⟨ρ.asAlgebraHom (eps Q * MonoidAlgebra.of K G g) y, ?_⟩
  conv_rhs => rw [← hy]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  calc eps Q * eS T s * (eps Q * MonoidAlgebra.of K G g)
      = eps Q * ((eps Q * MonoidAlgebra.of K G g) * eS T s) := by rw [mul_assoc, eS_comm]
    _ = (eps Q * eps Q) * MonoidAlgebra.of K G g * eS T s := by simp only [mul_assoc]
    _ = eps Q * MonoidAlgebra.of K G g * eS T s := by rw [eps_idem]
end PI.Dv.Tr
