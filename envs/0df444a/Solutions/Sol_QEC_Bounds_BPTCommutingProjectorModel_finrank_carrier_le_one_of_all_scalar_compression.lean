-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finrank_carrier_le_one_of_all_scalar_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:42:57.36274+00:00
-- url     : https://prove2.me/submissions/5948c099-3e89-48fb-8b63-b9f09a6fb07d

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (C : Semantics.QuantumCode H)
    (hscalar : ∀ A : Semantics.Operator H, ∃ scalar : Complex,
      C.projector * A * C.projector = scalar • C.projector) :
    Module.finrank Complex C.carrier ≤ 1 := by
  by_contra hle
  have hdim : 1 < Module.finrank Complex C.carrier := Nat.lt_of_not_ge hle
  have hpositive : 0 < Module.finrank Complex C.carrier := by omega
  rcases Module.finrank_pos_iff_exists_ne_zero.mp hpositive with ⟨x, hx⟩
  rcases exists_linearIndependent_pair_of_one_lt_finrank hdim hx with ⟨y, hxy⟩
  let A : Semantics.Operator H :=
    (InnerProductSpace.rankOne Complex (x : H) (x : H)).toLinearMap
  rcases hscalar A with ⟨scalar, hscalarA⟩
  have hpx : C.projector (x : H) = x := C.projector_eq_self_of_mem x.property
  have hpy : C.projector (y : H) = y := C.projector_eq_self_of_mem y.property
  have hxambient : (x : H) ≠ 0 := by
    intro hzero
    exact hx (Subtype.ext hzero)
  have hleftx : (C.projector * A * C.projector) (x : H) =
      (inner Complex (x : H) (x : H)) • (x : H) := by
    change C.projector (A (C.projector (x : H))) = _
    rw [hpx]
    simp [A, InnerProductSpace.rankOne_apply, hpx]
  have hrightx : (scalar • C.projector) (x : H) = scalar • (x : H) := by
    rw [LinearMap.smul_apply, hpx]
  have hxEq : (inner Complex (x : H) (x : H)) • (x : H) = scalar • (x : H) := by
    calc
      (inner Complex (x : H) (x : H)) • (x : H) =
          (C.projector * A * C.projector) (x : H) := hleftx.symm
      _ = (scalar • C.projector) (x : H) := congrArg (fun operator => operator (x : H)) hscalarA
      _ = scalar • (x : H) := hrightx
  have hscalarEq : inner Complex (x : H) (x : H) = scalar :=
    smul_left_injective Complex hxambient hxEq
  have hlefty : (C.projector * A * C.projector) (y : H) =
      (inner Complex (x : H) (y : H)) • (x : H) := by
    change C.projector (A (C.projector (y : H))) = _
    rw [hpy]
    simp [A, InnerProductSpace.rankOne_apply, hpx]
  have hrighty : (scalar • C.projector) (y : H) = scalar • (y : H) := by
    rw [LinearMap.smul_apply, hpy]
  have hyEq : (inner Complex (x : H) (y : H)) • (x : H) = scalar • (y : H) := by
    calc
      (inner Complex (x : H) (y : H)) • (x : H) =
          (C.projector * A * C.projector) (y : H) := hlefty.symm
      _ = (scalar • C.projector) (y : H) := congrArg (fun operator => operator (y : H)) hscalarA
      _ = scalar • (y : H) := hrighty
  have hinner : inner Complex (x : H) (x : H) ≠ 0 := inner_self_ne_zero.mpr hxambient
  have hyDependent :
      ((inner Complex (x : H) (y : H) / inner Complex (x : H) (x : H)) • x : C.carrier) = y := by
    apply Subtype.ext
    change (inner Complex (x : H) (y : H) / inner Complex (x : H) (x : H)) • (x : H) = (y : H)
    calc
      (inner Complex (x : H) (y : H) / inner Complex (x : H) (x : H)) • (x : H) =
          (inner Complex (x : H) (x : H))⁻¹ •
            ((inner Complex (x : H) (y : H)) • (x : H)) := by
              rw [div_eq_mul_inv, mul_comm, smul_smul]
      _ = (inner Complex (x : H) (x : H))⁻¹ •
            ((inner Complex (x : H) (x : H)) • (y : H)) := by rw [hyEq, ← hscalarEq]
      _ = (y : H) := by rw [smul_smul, inv_mul_cancel₀ hinner, one_smul]
  exact ((LinearIndependent.pair_iff' hx).mp hxy _ hyDependent)
end QEC.Bounds.BPTCommutingProjectorModel
