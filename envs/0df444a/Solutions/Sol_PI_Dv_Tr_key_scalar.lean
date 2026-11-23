-- Prove2me | solution 1 for PI.Dv.Tr.key_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:23:58.028095+00:00
-- url     : https://prove2.me/submissions/5177af62-32df-45b0-85bb-ab72d5cc4ecb

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
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
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
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
variable (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (cB : MonoidAlgebra K G → K)
  (g h : Fin (nS T P s) → G)
  (hlift : ∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s))
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
include hlift
namespace PI.Dv.Tr
theorem _root_.solution (a : MonoidAlgebra K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) :
    ρ.asAlgebraHom (eps P0 * a) y = cB a • y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Module.End.mul_apply, ← map_mul]
  have : eps P0 * a * (eps P0 * eS T s) = eps P0 * a * eps P0 * eS T s := by simp only [mul_assoc]
  rw [this, hlift, map_smul, LinearMap.smul_apply]
end PI.Dv.Tr
