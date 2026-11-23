-- Prove2me | solution 1 for PI.Dv.Tr.inj_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:00.053504+00:00
-- url     : https://prove2.me/submissions/1399f2fe-723c-498b-9709-4eee5f95e699

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
import Theorems.Thm_PI_Dv_Tr_key_scalar
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_Tr_unit_vec
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
theorem _root_.solution (hN : IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))))
    (y : Fin (nS T P s) → V) (hy : ∀ i, y i ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s)))
    (h0 : ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) (y i) = 0) : y = 0 := by
  apply unit_vec _ hN y
  intro j
  have := congrArg (ρ.asAlgebraHom (eps P0 * MonoidAlgebra.of K G (h j))) h0
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, ← map_mul,
    show eps P0 * MonoidAlgebra.of K G (h j) * (eps P * MonoidAlgebra.of K G (g i)) =
      eps P0 * (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i)) by simp only [mul_assoc],
    key_scalar T s P0 cB hlift ρ _ _ (hy i)]
  rfl
end PI.Dv.Tr
