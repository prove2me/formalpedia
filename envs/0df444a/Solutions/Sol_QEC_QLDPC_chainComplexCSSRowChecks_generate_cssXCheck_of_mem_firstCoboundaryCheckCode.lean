-- Prove2me | solution 1 for QEC.QLDPC.chainComplexCSSRowChecks_generate_cssXCheck_of_mem_firstCoboundaryCheckCode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:38:16.838868+00:00
-- url     : https://prove2.me/submissions/d3505196-1468-40b9-a4de-a617184d8ba2

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QLDPC_Core
import Theorems.Thm_QEC_QLDPC_generatedStabilizer_cssXCheck_sum
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
    {x : Coding.Word (ZMod 2) ι} (hx : x ∈ K.firstCoboundaryCheckCode.carrier) :
    Coding.PauliSymplectic.GeneratedStabilizer
      (fun g : {P : Coding.PauliSymplectic.Binary ι // P ∈ chainComplexCSSRowChecks K} => g.1)
      (Coding.PauliSymplectic.cssXCheck x) := by
  classical
  rcases (K.mem_firstCoboundaryCheckCode_iff x).1 hx with ⟨y, rfl⟩
  let generators :=
    fun g : {P : Coding.PauliSymplectic.Binary ι // P ∈ chainComplexCSSRowChecks K} => g.1
  change Coding.PauliSymplectic.GeneratedStabilizer generators
    (Coding.PauliSymplectic.cssXCheck (Coding.wordLinearMapTranspose K.boundary1 y))
  have hterm : ∀ k ∈ (Finset.univ : Finset κ),
      Coding.PauliSymplectic.GeneratedStabilizer generators
        (Coding.PauliSymplectic.cssXCheck
          (Coding.wordLinearMapTranspose K.boundary1 (Pi.single k (y k)))) := by
    intro k _hk
    by_cases hk0 : y k = 0
    · have hzero : Coding.wordLinearMapTranspose K.boundary1 (Pi.single k (y k)) = 0 := by
        simp [hk0]
      rw [hzero]
      simpa [Coding.PauliSymplectic.binaryOne] using
        (Coding.PauliSymplectic.GeneratedStabilizer.one (generators := generators))
    · have hk1 : y k = 1 := Coding.PauliSymplectic.zmod_two_eq_one_of_ne_zero hk0
      have hrow : chainComplexCSSRowCheck K (Sum.inl k) ∈ chainComplexCSSRowChecks K :=
        (mem_chainComplexCSSRowChecks K _).2 ⟨Sum.inl k, rfl⟩
      have hgenerator : Coding.PauliSymplectic.GeneratedStabilizer generators
          (chainComplexCSSRowCheck K (Sum.inl k)) :=
        Coding.PauliSymplectic.GeneratedStabilizer.generator
          (⟨chainComplexCSSRowCheck K (Sum.inl k), hrow⟩ :
            {P : Coding.PauliSymplectic.Binary ι // P ∈ chainComplexCSSRowChecks K})
      simpa [chainComplexCSSRowCheck, Coding.canonicalBasisWord, hk1] using hgenerator
  have hsum := generatedStabilizer_cssXCheck_sum generators Finset.univ
    (fun k : κ => Coding.wordLinearMapTranspose K.boundary1 (Pi.single k (y k))) hterm
  have hsum_eq :
      (∑ k ∈ (Finset.univ : Finset κ),
        Coding.wordLinearMapTranspose K.boundary1 (Pi.single k (y k))) =
      Coding.wordLinearMapTranspose K.boundary1 y := by
    rw [← map_sum, Coding.word_eq_sum_single]
  rw [hsum_eq] at hsum
  exact hsum
end QEC.QLDPC
