-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.operator_eq_sum_rankOne_matrix_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:52:57.343196+00:00
-- url     : https://prove2.me/submissions/3b6dfbf0-b95f-40fa-917e-07bf8be14874

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_operator_eq_sum_rankOne_basis
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] (b : OrthonormalBasis κ Complex H)
    (A : Operator H) :
    A = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
      (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
  calc
    A = ∑ i : κ, (InnerProductSpace.rankOne Complex (A (b i)) (b i)).toLinearMap :=
      operator_eq_sum_rankOne_basis H b A
    _ = ∑ i : κ, ∑ j : κ, inner Complex (b j) (A (b i)) •
        (InnerProductSpace.rankOne Complex (b j) (b i)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          ext x
          simp only [LinearMap.sum_apply, LinearMap.smul_apply]
          change inner Complex (b i) x • A (b i) =
            ∑ j : κ, inner Complex (b j) (A (b i)) • (inner Complex (b i) x • b j)
          calc
            inner Complex (b i) x • A (b i) = inner Complex (b i) x •
                ∑ j : κ, inner Complex (b j) (A (b i)) • b j := by
                  rw [b.sum_repr']
            _ = ∑ j : κ, inner Complex (b j) (A (b i)) •
                (inner Complex (b i) x • b j) := by
                  rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  simp [smul_smul, mul_comm]
end QEC.Semantics.QuditSubsystem
