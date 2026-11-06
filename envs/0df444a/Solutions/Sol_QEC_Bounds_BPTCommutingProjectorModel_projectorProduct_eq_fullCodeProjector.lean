-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_eq_fullCodeProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:10:53.672315+00:00
-- url     : https://prove2.me/submissions/3070ffd3-b60a-496f-8bdd-d9e712c6b427

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_fixed_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_idempotent
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_adjoint_eq_self
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProduct_adjoint_eq_self
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorProduct_mem_codeSpace
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_eq_self_of_mem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC
namespace Bounds
open Classical
open scoped BigOperators
universe u v
namespace BPTSquareLattice
end BPTSquareLattice
namespace BPTQuditLattice
end BPTQuditLattice
namespace BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]
private theorem projectorProduct_apply_eq_self_of_fixed
    (M : BPTCommutingProjectorModel L κ) (vector : L.Register)
    (hfixed : ∀ check, M.projector check vector = vector) :
    M.projectorProduct vector = vector := by
  unfold projectorProduct
  refine Finset.noncommProd_induction Finset.univ M.projector
    (M.projector_pairwise_commute Finset.univ) (fun product => product vector = vector) ?_ ?_ ?_
  · intro A B hA hB
    simp only [Module.End.mul_apply, hB, hA]
  · rfl
  · intro check _
    exact hfixed check
end BPTCommutingProjectorModel
end Bounds
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {κ : Type v} [Fintype κ]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (M : BPTCommutingProjectorModel L κ) :
    M.projectorProduct = M.fullCodeProjector := by
  have hproduct_after_code :
      M.projectorProduct.comp M.fullCodeProjector = M.fullCodeProjector := by
    apply LinearMap.ext
    intro vector
    change M.projectorProduct (M.fullCodeProjector vector) = M.fullCodeProjector vector
    apply M.projectorProduct_apply_eq_self_of_fixed
    intro check
    have hfixed : M.fullCodeProjector (M.fullCodeProjector vector) =
        M.fullCodeProjector vector :=
      congrArg (fun A : Semantics.Operator L.Register => A vector) M.fullCodeProjector_idempotent
    exact (M.fullCodeProjector_fixed_iff (M.fullCodeProjector vector)).1 hfixed check
  have hcode_after_product :
      M.fullCodeProjector.comp M.projectorProduct = M.projectorProduct := by
    apply LinearMap.ext
    intro vector
    change M.fullCodeProjector (M.projectorProduct vector) = M.projectorProduct vector
    exact M.codeSpace.projector_eq_self_of_mem (M.projectorProduct_mem_codeSpace vector)
  have hcode_after_product_eq_code :
      M.fullCodeProjector.comp M.projectorProduct = M.fullCodeProjector := by
    have hadjoint := congrArg LinearMap.adjoint hproduct_after_code
    simpa [LinearMap.adjoint_comp, M.projectorProduct_adjoint_eq_self,
      M.fullCodeProjector_adjoint_eq_self] using hadjoint
  calc
    M.projectorProduct = M.fullCodeProjector.comp M.projectorProduct := hcode_after_product.symm
    _ = M.fullCodeProjector := hcode_after_product_eq_code
end QEC.Bounds.BPTCommutingProjectorModel
