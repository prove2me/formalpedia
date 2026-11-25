-- Prove2me | solution 1 for PI.Dv.Tr.eS_in_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:03.173412+00:00
-- url     : https://prove2.me/submissions/d031e517-0df0-47a0-abc6-232f83661f3d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Theorems.Thm_PI_Dv_Tr_sandwich
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_Tr_mul_eS
import Theorems.Thm_PI_Dv_Tr_phiS_one
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
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) (P0 : Pair K G)
    (hY : (T.tau s).asAlgebraHom (eps P0) ≠ 0) :
    ∃ (n : ℕ) (a b : Fin n → MonoidAlgebra K G), ∑ i, a i * (eps P0 * (b i * eS T s)) = eS T s := by
  obtain ⟨n, A, B, h⟩ := sandwich _ hY
  choose a ha using fun i => T.irr s (A i)
  choose b hb using fun i => T.irr s (B i)
  refine ⟨n, a, b, ?_⟩
  have key : (∑ i, a i * eps P0 * b i) * eS T s = eS T s := by
    rw [mul_eS, map_sum]
    simp only [map_mul, ha, hb]
    rw [h, phiS_one]
  conv_rhs => rw [← key]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]
end PI.Dv.Tr
