-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.unitaryGroup_sum_star_col_mul_col_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:06.595015+00:00
-- url     : https://prove2.me/submissions/362c5268-57d6-4b64-9dd4-e113a98c32be

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_unitaryGroup_sum_star_col_mul_col
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
variable [DecidableEq ι]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {M : Type*} [AddCommMonoid M] [Module Complex M]
    (U : Matrix.unitaryGroup ι Complex) (B : ι → ι → M) :
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      (star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) • B i j) =
      ∑ i : ι, B i i := by
  classical
  calc
    (∑ a : ι, ∑ i : ι, ∑ j : ι,
      (star ((U : Matrix ι ι Complex) i a) *
        (U : Matrix ι ι Complex) j a) • B i j)
        = ∑ i : ι, ∑ a : ι, ∑ j : ι,
            (star ((U : Matrix ι ι Complex) i a) *
              (U : Matrix ι ι Complex) j a) • B i j := by
              rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι, ∑ a : ι,
            (star ((U : Matrix ι ι Complex) i a) *
              (U : Matrix ι ι Complex) j a) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ j : ι,
            (∑ a : ι,
              star ((U : Matrix ι ι Complex) i a) *
                (U : Matrix ι ι Complex) j a) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Finset.sum_smul]
    _ = ∑ i : ι, ∑ j : ι, (if i = j then 1 else 0 : Complex) • B i j := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [unitaryGroup_sum_star_col_mul_col]
    _ = ∑ i : ι, B i i := by
              simp
end QEC.Semantics.FiniteKrausFamily
