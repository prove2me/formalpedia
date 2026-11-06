-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.generatedStabilizer_css_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:45.304933+00:00
-- url     : https://prove2.me/submissions/7cdbe8ab-0dc9-4372-a6d8-253834fb767d

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι)
    (hdual : zCode.carrier ≤ xCode.dual.carrier)
    {κ : Type w} [Fintype κ] (generators : κ → Binary ι)
    (hgenerators : ∀ j, generators j ∈ binaryCSSCheckSet xCode zCode)
    {P : Binary ι} (hP : GeneratedStabilizer generators P) :
    P.phase = 0 ∧ P.vector.xPart ∈ xCode.carrier ∧
      P.vector.zPart ∈ zCode.carrier := by
  induction hP with
  | one =>
      exact ⟨rfl, xCode.carrier.zero_mem, zCode.carrier.zero_mem⟩
  | generator j =>
      rcases hgenerators j with ⟨x, hx, hj⟩ | ⟨z, hz, hj⟩
      · rw [hj]
        exact ⟨rfl, hx, zCode.carrier.zero_mem⟩
      · rw [hj]
        exact ⟨rfl, xCode.carrier.zero_mem, hz⟩
  | @mul P Q hP hQ ihP ihQ =>
      rcases ihP with ⟨hPphase, hPx, hPz⟩
      rcases ihQ with ⟨hQphase, hQx, hQz⟩
      have hcross :
          (∑ i, Q.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hQx (hdual hPz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryMul, binaryMulPhase, hPphase, hQphase, hcross]
      · simpa [binaryMul] using xCode.carrier.add_mem hPx hQx
      · simpa [binaryMul] using zCode.carrier.add_mem hPz hQz
  | @dagger P hP ihP =>
      rcases ihP with ⟨hphase, hx, hz⟩
      have hcross :
          (∑ i, P.vector.xPart i * P.vector.zPart i) = (0 : ZMod 2) := by
        simpa [wordPairing_apply, dotProduct] using
          xCode.dual_orthogonal hx (hdual hz)
      refine ⟨?_, ?_, ?_⟩
      · simp [binaryDagger, binaryDaggerPhase, hphase, hcross]
      · simpa [binaryDagger] using hx
      · simpa [binaryDagger] using hz
end QEC.Coding.PauliSymplectic
