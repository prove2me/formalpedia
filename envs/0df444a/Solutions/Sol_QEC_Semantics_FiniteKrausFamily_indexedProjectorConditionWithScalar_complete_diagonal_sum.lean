-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_complete_diagonal_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:43:19.054874+00:00
-- url     : https://prove2.me/submissions/20bc51b1-81f5-4e92-8b32-bb7851dd9de1

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hE : E.Complete)
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar) :
    (∑ i : ι, scalar i i) • C.projector = C.projector := by
  ext x
  calc
    ((∑ i : ι, scalar i i) • C.projector) x
        = ((∑ i : ι, scalar i i • C.projector) : Operator H) x := by
          rw [Finset.sum_smul]
    _ = ∑ i : ι, ((scalar i i • C.projector) x) := by
          simp
    _ = ∑ i : ι,
          (((C.projector.comp
            ((LinearMap.adjoint (E.operator i)).comp (E.operator i))).comp
              C.projector) x) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact congrArg (fun A : Operator H => A x) (hKL i i).symm
    _ = C.projector
          ((∑ i : ι, (LinearMap.adjoint (E.operator i)).comp (E.operator i))
            (C.projector x)) := by
          simp [LinearMap.comp_apply, Finset.sum_apply]
    _ = C.projector x := by
          rw [hE]
          exact C.projector_eq_self_of_mem (C.projector_mem_carrier x)
end QEC.Semantics.FiniteKrausFamily
