-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:59:00.814939+00:00
-- url     : https://prove2.me/submissions/b6886ae5-9e15-435a-a32a-0b3db97e4522

import Definitions.Def_QEC_Import_Compact_a7c59a129dc32b69
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor

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
theorem _root_.QEC.QECertImportCore.proof_a7c59a129dc32b69
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (a : M.fourFactorA region) (b : M.fourFactorB region)
    (c : M.fourFactorC region) (d : M.fourFactorD region) :
    (M.fourFactorMiddleReassociate region).symm.toLinearEquiv
        ((boundaryToMiddleReorder (M.fourFactorA region) (M.fourFactorB region)
            (M.fourFactorC region) (M.fourFactorD region)).toLinearEquiv
          ((b ⊗ₜ[Complex] c) ⊗ₜ[Complex] (a ⊗ₜ[Complex] d))) =
      a ⊗ₜ[Complex] (b ⊗ₜ[Complex] (c ⊗ₜ[Complex] d)) := by
  rw [boundaryToMiddleReorder_toLinearEquiv_apply_tmul]
  exact M.fourFactorMiddleReassociate_symm_toLinearEquiv_apply_tmul region a b c d
end QEC.Bounds.BPTCommutingProjectorModel

end

universe checked_u0
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.boundaryToFourFactorReorder_toLinearEquiv_apply_tmul_QECertStatement.{checked_u0} := @QEC.QECertImportCore.proof_a7c59a129dc32b69.{checked_u0}
