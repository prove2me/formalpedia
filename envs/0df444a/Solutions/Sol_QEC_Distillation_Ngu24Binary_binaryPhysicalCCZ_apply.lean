-- Prove2me | solution 1 for QEC.Distillation.Ngu24Binary.binaryPhysicalCCZ_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:58:50.460043+00:00
-- url     : https://prove2.me/submissions/8b4e8ecb-7813-40e2-a748-afe27f84c65c

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CubicPhase
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryPhysicalCCZ
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi2_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryPi3_symm_apply
import Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCCZ_taggedCubicPhaseTransport_apply
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
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi2_symm_apply
attribute [local simp] QEC.Distillation.Ngu24Binary.binaryPi3_symm_apply
attribute [local simp] QEC.Distillation.Ngu24MultiplicativeCCZ.taggedCubicPhaseTransport_apply
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


section
noncomputable section
namespace QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
private theorem composeBinaryTriples_apply (sites : List (J × Fin 512))
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    UnitaryTransport.composeList (sites.map binaryTripleCCZ) psi label =
      (sites.map fun x => binaryTripleAmplitude x label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons x xs ih =>
    change UnitaryTransport.composeList (xs.map binaryTripleCCZ)
      (binaryTripleCCZ x psi) label = _
    rw [ih]
    simp only [binaryTripleCCZ_apply, List.map_cons, List.prod_cons]
    ring
end QEC.Distillation.Ngu24Binary
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics
open scoped BigOperators
variable {J : Type} [Fintype J] [DecidableEq J]
namespace QEC.Distillation.Ngu24Binary
theorem _root_.solution
    (psi : TaggedThreeCopyRegister (ZMod 2) (J × Fin 512))
    (label : TaggedThreeCopyRegisterLabel (ZMod 2) (J × Fin 512)) :
    binaryPhysicalCCZ psi label =
      PauliSymplectic.binaryPhaseScalar (binarySelectedExponent label) * psi label := by
  unfold binaryPhysicalCCZ UnitaryTransport.composeFamily
  have hlist : List.ofFn (fun j => binaryTripleCCZ (binarySelectedSiteEquivFin J j).val) =
      (List.ofFn (fun j => (binarySelectedSiteEquivFin J j).val)).map binaryTripleCCZ := by
    rw [List.map_ofFn]
    rfl
  rw [hlist, composeBinaryTriples_apply, List.map_ofFn, Fin.prod_ofFn]
  congr 1
  rw [binarySelectedExponent, PauliSymplectic.binaryPhaseScalar_sum]
  calc
    _ = ∏ x : {x // x ∈ binarySelectedSites J}, binaryTripleAmplitude x.val label :=
      Fintype.prod_equiv (binarySelectedSiteEquivFin J) _ _ (fun _ => rfl)
    _ = ∏ x ∈ binarySelectedSites J, PauliSymplectic.binaryPhaseScalar
        (binaryTripleExponent x label) := by
      exact (Finset.prod_subtype (binarySelectedSites J) (fun _ => Iff.rfl)
        (fun x => binaryTripleAmplitude x label)).symm
end QEC.Distillation.Ngu24Binary
