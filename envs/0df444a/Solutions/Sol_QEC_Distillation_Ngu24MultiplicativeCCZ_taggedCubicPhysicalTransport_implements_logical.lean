-- Prove2me | solution 1 for QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhysicalTransport_implements_logical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:43:02.756207+00:00
-- url     : https://prove2.me/submissions/c0b67bc5-4b98-476e-8f62-aff49d336d77

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CCZIntertwining
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhysicalTransport_apply_coset
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_assembleTagged_extractBlock
import Theorems.Thm_QEC_Distillation_extractBlock_assembleTagged
import Theorems.Thm_QEC_Distillation_mem_coordinateSupport
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_taggedCczLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_taggedCczTransport_apply
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
attribute [local simp] QEC.Distillation.assembleTagged_extractBlock
attribute [local simp] QEC.Distillation.extractBlock_assembleTagged
attribute [local simp] QEC.Distillation.mem_coordinateSupport
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_apply
attribute [local simp] QEC.Distillation.taggedCczLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.taggedCczTransport_apply
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


attribute [local simp] QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCCZ
open Coding Semantics Ngu24MultiplicativeCSS
open scoped BigOperators
universe u
variable {F J I Logical : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
  [Fintype J] [DecidableEq J]
variable [Fintype I] [Fintype Logical] [CharP F 2]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCCZ._p2m_local_instance_bfada1b37a_179
namespace QEC.Distillation.Ngu24MultiplicativeCCZ
theorem _root_.solution (data : SourceInput F I Logical)
    (f : F →ₗ[ZMod 2] ZMod 2) :
    (taggedEncodedCode data).ImplementsLogicalGate
      (taggedCubicPhysicalTransport f)
      (taggedCubicPhaseTransport f Finset.univ) := by
  intro psi
  change taggedCubicPhysicalTransport f (taggedEncodingLinearMap data psi) =
    taggedEncodingLinearMap data (taggedCubicPhaseTransport f Finset.univ psi)
  change taggedCubicPhysicalTransport f
      (∑ label : TaggedThreeCopyRegisterLabel F Logical,
        psi label • taggedShortenedCosetKet data label) = _
  rw [map_sum]
  simp_rw [map_smul, taggedCubicPhysicalTransport_apply_coset]
  change (∑ label : TaggedThreeCopyRegisterLabel F Logical,
      psi label • (taggedCubicPhaseAmplitude f Finset.univ label •
        taggedShortenedCosetKet data label)) =
    ∑ label : TaggedThreeCopyRegisterLabel F Logical,
      (taggedCubicPhaseTransport f Finset.univ psi) label • taggedShortenedCosetKet data label
  apply Finset.sum_congr rfl
  intro label _
  rw [taggedCubicPhaseTransport_apply, smul_smul, mul_comm]
end QEC.Distillation.Ngu24MultiplicativeCCZ
