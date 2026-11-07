-- Prove2me | solution 1 for QEC.Distillation.taggedCczPhysicalTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:11:31.845796+00:00
-- url     : https://prove2.me/submissions/b8cfd94b-c667-4e41-8376-195163c4bf3b

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Phase
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_PhysicalCCZ
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


section
noncomputable section
namespace QEC.Distillation
open Semantics
open scoped BigOperators
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
private theorem composeTaggedCczTransports_apply [Fintype ι] [DecidableEq ι]
    (sites : List ι) (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    UnitaryTransport.composeList (sites.map taggedCczTransport) psi label =
      (sites.map fun site => taggedCczAmplitude site label).prod * psi label := by
  induction sites generalizing psi with
  | nil => simp [UnitaryTransport.composeList]
  | cons site sites ih =>
      change UnitaryTransport.composeList (sites.map taggedCczTransport)
          (taggedCczTransport site psi) label = _
      rw [ih]
      simp only [taggedCczTransport_apply, List.map_cons, List.prod_cons]
      ring
end QEC.Distillation
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped BigOperators
universe u
variable {F ι : Type u} [Field F] [Fintype F] [Algebra (ZMod 2) F]
namespace QEC.Distillation
theorem _root_.solution [Fintype ι] [DecidableEq ι]
    (psi : TaggedThreeCopyRegister F ι)
    (label : TaggedThreeCopyRegisterLabel F ι) :
    taggedCczPhysicalTransport psi label =
      (∏ site : ι, taggedCczAmplitude site label) * psi label := by
  rw [taggedCczPhysicalTransport, UnitaryTransport.composeFamily]
  have hlist :
      List.ofFn (fun j : Fin (Fintype.card ι) =>
        taggedCczTransport (taggedCczSiteEquivFin ι j)) =
        (List.ofFn (taggedCczSiteEquivFin ι)).map (taggedCczTransport (F := F)) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [hlist, composeTaggedCczTransports_apply]
  rw [List.map_ofFn, Fin.prod_ofFn]
  congr 1
  exact Fintype.prod_equiv (taggedCczSiteEquivFin ι) _ _ (fun _ => rfl)
end QEC.Distillation
