-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSSyndrome_eq_classicalSyndromes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:18:23.902679+00:00
-- url     : https://prove2.me/submissions/fd0cb779-a5c8-4b52-a49a-16e0e447c43c

import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Definitions.Def_QEC_Coding_CSS_Syndrome
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_apply
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



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
universe v
variable {ι κP κQ : Type v} [Fintype ι] [Fintype κP] [Fintype κQ]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (P : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κP)
    (Q : Word (ZMod 2) ι →ₗ[ZMod 2] Word (ZMod 2) κQ)
    (horth : ∀ p q,
      wordPairing (parityCheckRow P p) (parityCheckRow Q q) = 0)
    (E : Binary ι) :
    stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E =
      Sum.elim (P E.vector.xPart) (Q E.vector.zPart) := by
  classical
  funext j
  cases j with
  | inl p =>
      calc
        stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E (Sum.inl p) =
            wordPairing E.vector.xPart (parityCheckRow P p) := by
              simp [stabilizerSyndrome, stabilizerSyndromeBit,
                binaryCSSParityCheckGenerators, symplecticForm,
                wordPairing_apply, dotProduct]
        _ = wordPairing (parityCheckRow P p) E.vector.xPart := by
              simp [wordPairing_apply, dotProduct_comm]
        _ = wordPairing (Pi.single p 1) (P E.vector.xPart) :=
              wordPairing_wordLinearMapTranspose P (Pi.single p 1) E.vector.xPart
        _ = P E.vector.xPart p := by simp [wordPairing_apply]
        _ = Sum.elim (P E.vector.xPart) (Q E.vector.zPart) (Sum.inl p) := rfl
  | inr q =>
      calc
        stabilizerSyndrome (binaryCSSParityCheckGenerators P Q) E (Sum.inr q) =
            -wordPairing E.vector.zPart (parityCheckRow Q q) := by
              simp [stabilizerSyndrome, stabilizerSyndromeBit,
                binaryCSSParityCheckGenerators, symplecticForm,
                wordPairing_apply, dotProduct]
        _ = -wordPairing (parityCheckRow Q q) E.vector.zPart := by
              simp [wordPairing_apply, dotProduct_comm]
        _ = -wordPairing (Pi.single q 1) (Q E.vector.zPart) := by
              exact congrArg Neg.neg
                (wordPairing_wordLinearMapTranspose Q (Pi.single q 1) E.vector.zPart)
        _ = -(Q E.vector.zPart q) := by simp [wordPairing_apply]
        _ = Q E.vector.zPart q := ZMod.neg_eq_self_mod_two _
        _ = Sum.elim (P E.vector.xPart) (Q E.vector.zPart) (Sum.inr q) := rfl
end QEC.Coding.PauliSymplectic
