-- Prove2me | solution 1 for QEC.QLDPC.chainComplexCSSRowChecks_generate_cssZCheck_of_mem_middleBoundaryCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:38:18.03954+00:00
-- url     : https://prove2.me/submissions/c519840c-5b14-4d42-bfc6-6974420799e5

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_generatedStabilizer_cssZCheck_sum
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_checkSupport
import Theorems.Thm_QEC_QLDPC_CheckIncidence_mem_variableSupport
import Theorems.Thm_QEC_QLDPC_mem_chainComplexCSSRowChecks
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
      (Coding.Word (ZMod 2) lambda))
    {z : Coding.Word (ZMod 2) ι} (hz : z ∈ K.middleBoundaryCode.carrier) :
    Coding.PauliSymplectic.GeneratedStabilizer
      (fun g : {P : Coding.PauliSymplectic.Binary ι // P ∈ chainComplexCSSRowChecks K} => g.1)
      (Coding.PauliSymplectic.cssZCheck z) := by
  classical
  rcases (K.mem_middleBoundaryCode_iff z).1 hz with ⟨y, rfl⟩
  let generators :=
    fun g : {P : Coding.PauliSymplectic.Binary ι // P ∈ chainComplexCSSRowChecks K} => g.1
  change Coding.PauliSymplectic.GeneratedStabilizer generators
    (Coding.PauliSymplectic.cssZCheck (K.boundary2 y))
  have hterm : ∀ l ∈ (Finset.univ : Finset lambda),
      Coding.PauliSymplectic.GeneratedStabilizer generators
        (Coding.PauliSymplectic.cssZCheck (K.boundary2 (Pi.single l (y l)))) := by
    intro l _hl
    by_cases hl0 : y l = 0
    · have hzero : K.boundary2 (Pi.single l (y l)) = 0 := by
        simp [hl0]
      rw [hzero]
      simpa [Coding.PauliSymplectic.binaryOne] using
        (Coding.PauliSymplectic.GeneratedStabilizer.one (generators := generators))
    · have hl1 : y l = 1 := Coding.PauliSymplectic.zmod_two_eq_one_of_ne_zero hl0
      have hrow : chainComplexCSSRowCheck K (Sum.inr l) ∈ chainComplexCSSRowChecks K :=
        (mem_chainComplexCSSRowChecks K _).2 ⟨Sum.inr l, rfl⟩
      have hgenerator : Coding.PauliSymplectic.GeneratedStabilizer generators
          (chainComplexCSSRowCheck K (Sum.inr l)) :=
        Coding.PauliSymplectic.GeneratedStabilizer.generator
          (⟨chainComplexCSSRowCheck K (Sum.inr l), hrow⟩ :
            {P : Coding.PauliSymplectic.Binary ι // P ∈ chainComplexCSSRowChecks K})
      simpa [chainComplexCSSRowCheck, Coding.canonicalBasisWord, hl1] using hgenerator
  have hsum := generatedStabilizer_cssZCheck_sum generators Finset.univ
    (fun l : lambda => K.boundary2 (Pi.single l (y l))) hterm
  have hsum_eq :
      (∑ l ∈ (Finset.univ : Finset lambda), K.boundary2 (Pi.single l (y l))) =
      K.boundary2 y := by
    rw [← map_sum, Coding.word_eq_sum_single]
  rw [hsum_eq] at hsum
  exact hsum
end QEC.QLDPC
