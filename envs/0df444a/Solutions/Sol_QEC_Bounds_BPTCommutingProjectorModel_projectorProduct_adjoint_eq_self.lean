-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_adjoint_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:26.903819+00:00
-- url     : https://prove2.me/submissions/70a2569a-9d86-45b4-b468-9ac8cf081b70

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_adjoint_eq_self
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_adjoint_eq_self
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
private theorem projectorProductOn_adjoint_eq_self (M : BPTCommutingProjectorModel L κ)
    (checks : Finset κ)
    (hcomm : (checks : Set κ).Pairwise (Function.onFun Commute M.projector)) :
    LinearMap.adjoint (checks.noncommProd M.projector hcomm) =
      checks.noncommProd M.projector hcomm := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      simp [Finset.noncommProd_empty]
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set κ).Pairwise (Function.onFun Commute M.projector) :=
        hcomm.mono (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector hcomm =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector hcomm hnotmem]
      have hcommRest : Commute (M.projector check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute checks M.projector hrest (M.projector check)
          (fun other _ => M.projector_commute check other)
      calc
        LinearMap.adjoint ((insert check checks).noncommProd M.projector hcomm) =
            LinearMap.adjoint (M.projector check * productRest) := by rw [hfactor]
        _ = LinearMap.adjoint productRest * LinearMap.adjoint (M.projector check) := by
          rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, ← Module.End.mul_eq_comp]
        _ = productRest * M.projector check := by
          rw [show LinearMap.adjoint productRest = productRest by
            dsimp [productRest]
            exact induction hrest, M.projector_adjoint_eq_self]
        _ = M.projector check * productRest := hcommRest.eq.symm
        _ = (insert check checks).noncommProd M.projector hcomm := hfactor.symm
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
    LinearMap.adjoint M.projectorProduct = M.projectorProduct :=
  M.projectorProductOn_adjoint_eq_self Finset.univ
    (M.projector_pairwise_commute Finset.univ)
end QEC.Bounds.BPTCommutingProjectorModel
