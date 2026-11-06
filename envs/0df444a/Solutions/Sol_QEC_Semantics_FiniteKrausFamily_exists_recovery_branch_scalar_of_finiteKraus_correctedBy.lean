-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.exists_recovery_branch_scalar_of_finiteKraus_correctedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:36:52.812194+00:00
-- url     : https://prove2.me/submissions/563a16c3-a833-4740-bb7b-70c8bdb73500

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_operator_scalar_on_code_of_forall_mem_span
import Theorems.Thm_QEC_Semantics_FiniteKrausFamily_recovery_branch_mem_span_of_finiteKraus_correctedBy
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
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
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
    (_hR_complete : ∑ r : κ, (LinearMap.adjoint (R r)).comp (R r) = 1)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
        rho.toOperator) :
    ∃ branchScalar : κ → ι → Complex,
      ∀ r i (x : H), x ∈ C.carrier →
        R r (E.operator i x) = branchScalar r i • x := by
  classical
  have hscalar : ∀ r i : _, ∃ scalar : Complex,
      ∀ (x : H), x ∈ C.carrier → ((R r).comp (E.operator i)) x = scalar • x := by
    intro r i
    exact operator_scalar_on_code_of_forall_mem_span ((R r).comp (E.operator i)) C
      (fun x hx => recovery_branch_mem_span_of_finiteKraus_correctedBy E C R hcorrect r i hx)
  choose branchScalar hbranch using hscalar
  refine ⟨branchScalar, ?_⟩
  intro r i x hx
  simpa [LinearMap.comp_apply] using hbranch r i x hx
end QEC.Semantics.FiniteKrausFamily
