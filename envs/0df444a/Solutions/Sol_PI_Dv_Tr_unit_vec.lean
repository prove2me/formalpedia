-- Prove2me | solution 1 for PI.Dv.Tr.unit_vec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:03.861163+00:00
-- url     : https://prove2.me/submissions/8aa8a7eb-7e5a-4ab9-8856-45741878c226

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
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
open PI.Dv Module
variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
namespace PI.Dv.Tr
theorem _root_.solution {n : ℕ} {V : Type} [AddCommGroup V] [Module K V] (N : Matrix (Fin n) (Fin n) K) (hN : IsUnit N)
    (y : Fin n → V) (h : ∀ j, ∑ i, N j i • y i = 0) : y = 0 := by
  classical
  funext i
  have hinv : N⁻¹ * N = 1 := Matrix.nonsing_inv_mul N ((Matrix.isUnit_iff_isUnit_det N).mp hN)
  calc y i = ∑ k, (1 : Matrix (Fin n) (Fin n) K) i k • y k := by simp [Matrix.one_apply]
    _ = ∑ k, (N⁻¹ * N) i k • y k := by rw [hinv]
    _ = ∑ j, N⁻¹ i j • ∑ k, N j k • y k := by
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
    _ = 0 := by simp [h]
end PI.Dv.Tr
