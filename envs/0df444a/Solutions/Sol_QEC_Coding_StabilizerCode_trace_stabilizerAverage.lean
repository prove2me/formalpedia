-- Prove2me | solution 1 for QEC.Coding.StabilizerCode.trace_stabilizerAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:28:47.537194+00:00
-- url     : https://prove2.me/submissions/bb3dba9f-789f-4363-a88a-ec4c5a096882

import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Coding_Stabilizer_Symplectic
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Definitions.Def_QEC_Coding_Stabilizer_Detectability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_exists_mem_orthogonal_pairing_ne_zero
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_one
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_checkSupport_inr
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inl
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_incident_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_eq_checkSupport
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_support_inr
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inl
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_weight_inr
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.FiniteSymplectic.form_apply
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_checkSupport_inr
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inl
attribute [local simp] QEC.QLDPC.chainComplexBoundaryIncidence_incident_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_eq_checkSupport
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_support_inr
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inl
attribute [local simp] QEC.QLDPC.chainComplexCSSRowCheck_weight_inr
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Coding
universe u
namespace PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
end PauliSymplectic
namespace StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
private theorem binaryOne_vector_eq_zero :
    (binaryOne (ι := ι)).vector = (0 : SymplecticVector (ZMod 2) ι) := by
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
  simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binaryOne]
omit [DecidableEq ι] in
private theorem binarySign_vector_eq_zero (p : ZMod 2) :
    (binarySign (ι := ι) p).vector = (0 : SymplecticVector (ZMod 2) ι) := by
  apply (SymplecticVector.toProdLinearEquiv (F := ZMod 2) (ι := ι)).injective
  simp [SymplecticVector.toProdLinearEquiv, SymplecticVector.toProdEquiv, binarySign]
private theorem generatedGroupElement_eq_one_of_vector_eq_zero
    (Q : SourceValidBinary ι) (P : Q.1.GeneratedGroupElement)
    (hvector : P.1.vector = 0) : P = 1 := by
  by_cases hphase : P.1.phase = 0
  · apply Subtype.ext
    rw [PauliSymplectic.mk.injEq]
    exact ⟨hphase, hvector.trans binaryOne_vector_eq_zero.symm⟩
  · have hphaseOne : P.1.phase = 1 := zmod_two_eq_one_of_ne_zero hphase
    have hsign : P.1 = binarySign (ι := ι) 1 := by
      rw [PauliSymplectic.mk.injEq]
      exact ⟨hphaseOne, hvector.trans (binarySign_vector_eq_zero 1).symm⟩
    exact False.elim (Q.2.1 (hsign ▸ P.2))
private theorem trace_toQubitOperator_eq_zero_of_vector_ne_zero
    {P : Binary ι} (hvector : P.vector ≠ 0) :
    LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (toQubitOperator P) = 0 := by
  have houtside : P.vector ∉ (⊥ : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) := by
    simpa using hvector
  have horthogonal :
      P.vector ∈ FiniteSymplectic.form.orthogonal
        (⊥ : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι)) := by
    simp
  obtain ⟨r, _hrOrthogonal, hpair⟩ :=
    FiniteSymplectic.exists_mem_orthogonal_pairing_ne_zero
      (⊥ : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι))
      horthogonal houtside
  let R : Binary ι := { phase := 0, vector := r }
  let A := toQubitOperator P
  let B := toQubitOperator R
  let Binv := toQubitOperator (binaryDagger R)
  have hNotCommutes : ¬ Commutes P R := by
    simpa [R, Commutes] using hpair
  have hAB : A * B = -(B * A) := by
    simpa [A, B] using toQubitOperator_anticommute_of_not_commutes P R hNotCommutes
  have hBinvB : Binv * B = 1 := by
    change toQubitOperator (binaryDagger R) * toQubitOperator R = 1
    rw [← toQubitOperator_binaryMul]
    simp [toQubitOperator_one]
  have hBBinv : B * Binv = 1 := by
    change toQubitOperator R * toQubitOperator (binaryDagger R) = 1
    rw [← toQubitOperator_binaryMul]
    simp [toQubitOperator_one]
  let a : Complex := LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) A
  have haNeg : a = -a := by
    calc
      a = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (A * 1) := by
        simp [a]
      _ = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (A * (B * Binv)) := by
        rw [hBBinv]
      _ = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) ((A * B) * Binv) := by
        rw [mul_assoc]
      _ = LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (-(B * A) * Binv) := by
        rw [hAB]
      _ = -LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) ((B * A) * Binv) := by
        simp
      _ = -LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) (Binv * B * A) := by
        rw [LinearMap.trace_mul_cycle]
      _ = -a := by rw [hBinvB, one_mul]
  have hAdd : a + a = 0 := eq_neg_iff_add_eq_zero.mp haNeg
  have hTwo : (2 : Complex) * a = 0 := by simpa [two_mul] using hAdd
  have haZero : a = 0 := (mul_eq_zero.mp hTwo).resolve_left (by norm_num)
  simpa [a, A] using haZero
end StabilizerCode
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
universe u
open QEC.Coding.StabilizerCode
open PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.StabilizerCode
theorem _root_.solution
    (Q : SourceValidBinary ι) :
    LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι) Q.1.stabilizerAverage =
      (2 ^ Fintype.card ι : Nat) := by
  rw [stabilizerAverage, map_sum]
  rw [Fintype.sum_eq_single (1 : Q.1.GeneratedGroupElement)]
  · change LinearMap.trace Complex (Semantics.Qubit.QubitRegister ι)
      (toQubitOperator (binaryOne (ι := ι))) = _
    rw [toQubitOperator_one, LinearMap.trace_one, Semantics.Qubit.finrank_qubitRegister]
  · intro P hP
    apply trace_toQubitOperator_eq_zero_of_vector_ne_zero
    intro hvector
    exact hP (generatedGroupElement_eq_one_of_vector_eq_zero Q P hvector)
end QEC.Coding.StabilizerCode
