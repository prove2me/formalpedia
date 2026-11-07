-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSSyndrome_equalXZ_components_ne_zero_of_componentwiseSyndromeInjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:34:26.06448+00:00
-- url     : https://prove2.me/submissions/212a4e58-0571-421b-9d7a-259b3c15fea6

import Definitions.Def_QEC_Coding_CSS_Syndrome
import Definitions.Def_QEC_Coding_Stabilizer_Correctability
import Definitions.Def_QEC_Coding_CSS_Correctability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ_inl_ne_zero_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryCSSSyndrome_equalXZ_inr_ne_zero_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPauliKrausFamily_operator
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
attribute [local simp] QEC.Coding.PauliSymplectic.binaryPauliKrausFamily_operator
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
open QEC.Coding.PauliSymplectic
universe u v
variable {iota kappaP kappaQ : Type u} [Fintype iota] [DecidableEq iota]
  [Fintype kappaP] [Fintype kappaQ]
omit [DecidableEq iota]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaP)
    (Q : Word (ZMod 2) iota →ₗ[ZMod 2] Word (ZMod 2) kappaQ)
    (horth : ∀ p q, wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    {tX tZ : Nat}
    (hP : ∀ x y : Word (ZMod 2) iota,
      HammingWeight x ≤ tX → HammingWeight y ≤ tX → P x = P y → x = y)
    (hQ : ∀ z w : Word (ZMod 2) iota,
      HammingWeight z ≤ tZ → HammingWeight w ≤ tZ → Q z = Q w → z = w)
    (phase : ZMod 2) (y : Word (ZMod 2) iota)
    (hy : y ≠ 0) (hyX : HammingWeight y ≤ tX) (hyZ : HammingWeight y ≤ tZ) :
    P y ≠ 0 ∧ Q y ≠ 0 ∧
      stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
          ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota) =
        Sum.elim (P y) (Q y) ∧
      (fun p => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota)
        (Sum.inl p)) ≠ 0 ∧
      (fun q => stabilizerSyndrome (binaryCSSParityCheckGenerators P Q)
        ({ phase := phase, vector := { xPart := y, zPart := y } } : Binary iota)
        (Sum.inr q)) ≠ 0 := by
  have hPy : P y ≠ 0 := by
    intro hzero
    apply hy
    apply hP y 0 hyX (by simp)
    simpa using hzero
  have hQy : Q y ≠ 0 := by
    intro hzero
    apply hy
    apply hQ y 0 hyZ (by simp)
    simpa using hzero
  refine ⟨hPy, hQy, binaryCSSSyndrome_equalXZ P Q horth phase y, ?_, ?_⟩
  · exact (binaryCSSSyndrome_equalXZ_inl_ne_zero_iff P Q horth phase y).2 hPy
  · exact (binaryCSSSyndrome_equalXZ_inr_ne_zero_iff P Q horth phase y).2 hQy
end QEC.Coding.PauliSymplectic
