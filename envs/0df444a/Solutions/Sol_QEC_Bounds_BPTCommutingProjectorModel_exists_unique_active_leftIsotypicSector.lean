-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.exists_unique_active_leftIsotypicSector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:36.745606+00:00
-- url     : https://prove2.me/submissions/e31a485e-fa65-46fa-9538-90e66a4046af

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starSubalgebra_module_isSemisimple
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_apply_eq_self_of_mem
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A B : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (P : Semantics.Operator (Semantics.CompositeSystem A B)) (F : Semantics.Operator B)
    (hF : F ≠ 0)
    (hcommute : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
      Commute F (leftIsotypicSectorProjector P component))
    (hsector : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = 0 ∨
        F * leftIsotypicSectorProjector P component = F) :
    ∃ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = F ∧
        ∀ other : isotypicComponents (leftInteractionAlgebra P) B, other ≠ component →
          F * leftIsotypicSectorProjector P other = 0 := by
  classical
  letI : IsSemisimpleModule (leftInteractionAlgebra P) B :=
    starSubalgebra_module_isSemisimple (leftInteractionAlgebra P)
  have hsome : ∃ component : isotypicComponents (leftInteractionAlgebra P) B,
      F * leftIsotypicSectorProjector P component = F := by
    by_contra hnone
    push_neg at hnone
    have hzero : ∀ component : isotypicComponents (leftInteractionAlgebra P) B,
        F * leftIsotypicSectorProjector P component = 0 := by
      intro component
      exact (hsector component).resolve_right (hnone component)
    apply hF
    apply LinearMap.ext
    intro vector
    change F vector = (0 : B)
    have htop : (⨆ component : isotypicComponents (leftInteractionAlgebra P) B,
        component.1) = ⊤ :=
      (sSup_eq_iSup' _).symm.trans
        (sSup_isotypicComponents (leftInteractionAlgebra P) B)
    have hvector : vector ∈ ⨆ component : isotypicComponents (leftInteractionAlgebra P) B,
        component.1 := by
      rw [htop]
      trivial
    refine Submodule.iSup_induction (fun component :
      isotypicComponents (leftInteractionAlgebra P) B => component.1)
      (motive := fun x : B => F x = 0) hvector ?_ ?_ ?_
    · intro component member hmember
      have hfixed := leftIsotypicSectorProjector_apply_eq_self_of_mem P component hmember
      change F member = (0 : B)
      calc
        F member = F (leftIsotypicSectorProjector P component member) := by rw [hfixed]
        _ = (F * leftIsotypicSectorProjector P component) member := rfl
        _ = (0 : B) := by rw [hzero component]; rfl
    · exact F.map_zero
    · intro left right hleft hright
      simpa [map_add, hleft, hright]
  rcases hsome with ⟨component, hcomponent⟩
  refine ⟨component, hcomponent, ?_⟩
  intro other hother
  rcases hsector other with hzero | hactive
  · exact hzero
  · exfalso
    apply hF
    apply LinearMap.ext
    intro vector
    have hcomponentFixed :
        leftIsotypicSectorProjector P component (F vector) = F vector := by
      calc
        leftIsotypicSectorProjector P component (F vector) =
            F (leftIsotypicSectorProjector P component vector) := by
              exact congrArg (fun operator => operator vector) (hcommute component).eq.symm
        _ = F vector := congrArg (fun operator => operator vector) hcomponent
    have hotherFixed : leftIsotypicSectorProjector P other (F vector) = F vector := by
      calc
        leftIsotypicSectorProjector P other (F vector) =
            F (leftIsotypicSectorProjector P other vector) := by
              exact congrArg (fun operator => operator vector) (hcommute other).eq.symm
        _ = F vector := congrArg (fun operator => operator vector) hactive
    have hcomponentMem : F vector ∈ component.1 := by
      exact Submodule.starProjection_eq_self_iff.mp hcomponentFixed
    have hotherMem : F vector ∈ other.1 := by
      exact Submodule.starProjection_eq_self_iff.mp hotherFixed
    have hdisjoint : Disjoint component.1 other.1 :=
      (sSupIndep_isotypicComponents (leftInteractionAlgebra P) B).pairwiseDisjoint
        component.2 other.2 (by
          intro heq
          apply hother
          exact Subtype.ext heq.symm)
    simpa using hdisjoint.le_bot ⟨hcomponentMem, hotherMem⟩
end QEC.Bounds.BPTCommutingProjectorModel
