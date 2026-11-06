-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorProduct_mem_codeSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:08:33.803294+00:00
-- url     : https://prove2.me/submissions/a295ffc9-7a47-4852-bb3c-536cc0b0bf3b

import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_is_idempotent
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_codeSpace_iff
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
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
private theorem projectorProduct_mul_projector_eq
    (M : BPTCommutingProjectorModel L κ) (check : κ) :
    M.projectorProduct * M.projector check = M.projectorProduct := by
  classical
  let reduced : Semantics.Operator L.Register :=
    (Finset.univ.erase check).noncommProd M.projector
      (M.projector_pairwise_commute (Finset.univ.erase check))
  have hfactor : reduced * M.projector check = M.projectorProduct := by
    simpa [reduced, projectorProduct] using
      (Finset.noncommProd_erase_mul Finset.univ (Finset.mem_univ check)
        M.projector (M.projector_pairwise_commute Finset.univ))
  calc
    M.projectorProduct * M.projector check =
        (reduced * M.projector check) * M.projector check := by rw [hfactor]
    _ = reduced * (M.projector check * M.projector check) := by rw [mul_assoc]
    _ = reduced * M.projector check := by
      rw [show M.projector check * M.projector check = M.projector check by
        simpa [Module.End.mul_eq_comp] using M.projector_is_idempotent check]
    _ = M.projectorProduct := hfactor
private theorem projectorProduct_is_fixed
    (M : BPTCommutingProjectorModel L κ) (vector : L.Register) (check : κ) :
    M.projector check (M.projectorProduct vector) = M.projectorProduct vector := by
  have hcomm : Commute (M.projector check) M.projectorProduct := by
    unfold projectorProduct
    exact Finset.noncommProd_commute Finset.univ M.projector
      (M.projector_pairwise_commute Finset.univ) (M.projector check)
      (fun other _ => M.projector_commute check other)
  have hright := M.projectorProduct_mul_projector_eq check
  calc
    M.projector check (M.projectorProduct vector) =
        ((M.projector check * M.projectorProduct) vector) := rfl
    _ = ((M.projectorProduct * M.projector check) vector) := by rw [hcomm.eq]
    _ = M.projectorProduct vector := by
      exact congrArg (fun operator => operator vector) hright
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
theorem _root_.solution (M : BPTCommutingProjectorModel L κ)
    (vector : L.Register) : M.projectorProduct vector ∈ M.codeSpace.carrier := by
  exact M.mem_codeSpace_iff (M.projectorProduct vector) |>.2
    (fun check => M.projectorProduct_is_fixed vector check)
end QEC.Bounds.BPTCommutingProjectorModel
