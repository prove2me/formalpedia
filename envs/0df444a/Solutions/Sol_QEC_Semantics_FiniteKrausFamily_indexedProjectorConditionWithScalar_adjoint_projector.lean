-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_adjoint_projector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:47.717484+00:00
-- url     : https://prove2.me/submissions/95d66338-33d2-4bce-b676-4ea81d03b4ff

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
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
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar)
    (i j : ι) :
    star (scalar i j) • C.projector = scalar j i • C.projector := by
  have hij := hKL i j
  have hadj := congrArg LinearMap.adjoint hij
  have hAdjLeft :
      LinearMap.adjoint
          ((C.projector.comp ((LinearMap.adjoint (E.operator i)).comp
            (E.operator j))).comp C.projector) =
        (C.projector.comp ((LinearMap.adjoint (E.operator j)).comp
            (E.operator i))).comp C.projector := by
    ext x
    simp [LinearMap.adjoint_comp, C.projector_adjoint_eq_self,
      LinearMap.comp_apply]
  have hAdjRight :
      LinearMap.adjoint (scalar i j • C.projector) =
        star (scalar i j) • C.projector := by
    simpa [C.projector_adjoint_eq_self] using
      (map_smulₛₗ (LinearMap.adjoint : (Operator H) ≃ₗ⋆[Complex] Operator H)
        (scalar i j) C.projector)
  calc
    star (scalar i j) • C.projector
        = LinearMap.adjoint (scalar i j • C.projector) := hAdjRight.symm
    _ = LinearMap.adjoint
          ((C.projector.comp ((LinearMap.adjoint (E.operator i)).comp
            (E.operator j))).comp C.projector) := by
          rw [hij]
    _ = (C.projector.comp ((LinearMap.adjoint (E.operator j)).comp
            (E.operator i))).comp C.projector := hAdjLeft
    _ = scalar j i • C.projector := hKL j i
end QEC.Semantics.FiniteKrausFamily
