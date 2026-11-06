-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binaryCSSCheckSet_pairwise_commutes_iff_dual_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:29.503953+00:00
-- url     : https://prove2.me/submissions/f34837f8-d202-4bbe-99da-72f64c389a56

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
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



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution
    (xCode zCode : LinearCode (ZMod 2) ι) :
    (∀ P ∈ binaryCSSCheckSet xCode zCode,
      ∀ Q ∈ binaryCSSCheckSet xCode zCode, Commutes P Q) ↔
      zCode.carrier ≤ xCode.dual.carrier := by
  constructor
  · intro hcommutes z hz
    refine (xCode.mem_dual z).2 ?_
    intro x hx
    have hcommutesXZ : Commutes (cssXCheck x) (cssZCheck z) :=
      hcommutes
        (cssXCheck x) (Or.inl ⟨x, hx, rfl⟩)
        (cssZCheck z) (Or.inr ⟨z, hz, rfl⟩)
    have hpairXZ : wordPairing (F := ZMod 2) (ι := ι) x z = 0 := by
      simpa [cssXCheck, cssZCheck, Commutes,
        symplecticForm_x_zero_zero_z_eq_wordPairing] using hcommutesXZ
    simpa [wordPairing_apply, dotProduct_comm] using hpairXZ
  · exact binaryCSSCheckSet_pairwise_commutes_of_dual_le xCode zCode
end QEC.Coding.PauliSymplectic
