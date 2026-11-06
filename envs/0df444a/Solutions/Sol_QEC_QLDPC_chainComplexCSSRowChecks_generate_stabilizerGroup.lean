-- Prove2me | solution 1 for QEC.QLDPC.chainComplexCSSRowChecks_generate_stabilizerGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:42:11.316454+00:00
-- url     : https://prove2.me/submissions/eddfe81b-1687-4bb6-a339-9c38237a7653

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_generatedStabilizer_of_generators_generated
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowCheck_mem_binaryCSSCheckSet
import Theorems.Thm_QEC_QLDPC_chainComplexCSSRowChecks_generate_of_mem_binaryCSSCheckSet
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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


attribute [local simp] QEC.QLDPC.CheckIncidence.mem_checkSupport
attribute [local simp] QEC.QLDPC.CheckIncidence.mem_variableSupport
attribute [local simp] QEC.QLDPC.mem_chainComplexCSSRowChecks

set_option autoImplicit false
open QEC
universe u v w x
open scoped Classical
open QEC.QLDPC
namespace QEC.QLDPC
theorem _root_.solution
    {ι κ lambda : Type v} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype lambda]
    (K : Coding.ChainComplexData
      (ZMod 2) (Coding.Word (ZMod 2) κ) (Coding.Word (ZMod 2) ι)
      (Coding.Word (ZMod 2) lambda)) :
    FinsetGenerates (chainComplexCSSRowChecks K)
      (K.binaryCSSCode).stabilizer.generatedGroup := by
  classical
  letI : Fintype
      {Q : Coding.PauliSymplectic.Binary ι // Q ∈ (K.binaryCSSCode).stabilizer.stabilizers} :=
    Fintype.ofFinite _
  rw [FinsetGenerates]
  ext P
  constructor
  · intro hP
    change Coding.PauliSymplectic.GeneratedStabilizer
      (fun g : {Q : Coding.PauliSymplectic.Binary ι // Q ∈ chainComplexCSSRowChecks K} => g.1)
      P at hP
    unfold Coding.StabilizerCode.generatedGroup
    apply generatedStabilizer_of_generators_generated ?_ hP
    intro g
    have hg : g.1 ∈ (K.binaryCSSCode).stabilizer.stabilizers := by
      rcases (mem_chainComplexCSSRowChecks K g.1).1 g.2 with ⟨c, hc⟩
      rw [← hc]
      change chainComplexCSSRowCheck K c ∈
        Coding.PauliSymplectic.binaryCSSCheckSet
          K.firstCoboundaryCheckCode K.middleBoundaryCode
      exact chainComplexCSSRowCheck_mem_binaryCSSCheckSet K c
    exact Coding.PauliSymplectic.GeneratedStabilizer.generator
      (generators := fun check :
        {Q : Coding.PauliSymplectic.Binary ι // Q ∈ (K.binaryCSSCode).stabilizer.stabilizers} =>
          check.1)
      ⟨g.1, hg⟩
  · intro hP
    unfold Coding.StabilizerCode.generatedGroup at hP
    change Coding.PauliSymplectic.GeneratedStabilizer
      (fun g : {Q : Coding.PauliSymplectic.Binary ι // Q ∈ chainComplexCSSRowChecks K} => g.1)
      P
    apply generatedStabilizer_of_generators_generated ?_ hP
    intro check
    apply chainComplexCSSRowChecks_generate_of_mem_binaryCSSCheckSet K
    change check.1 ∈ Coding.PauliSymplectic.binaryCSSCheckSet
      K.firstCoboundaryCheckCode K.middleBoundaryCode
    exact check.2
end QEC.QLDPC
