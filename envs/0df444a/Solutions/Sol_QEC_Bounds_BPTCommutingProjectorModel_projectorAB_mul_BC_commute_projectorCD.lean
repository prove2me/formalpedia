-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_commute_projectorCD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:27:10.272399+00:00
-- url     : https://prove2.me/submissions/5574218d-ba9c-4a0f-a943-05c8ce799b38

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_commute_projectorCD
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorBC_commute_projectorCD

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    Commute (M.projectorAB region * M.projectorBC region) (M.projectorCD region) := by
  change (M.projectorAB region * M.projectorBC region) * M.projectorCD region =
    M.projectorCD region * (M.projectorAB region * M.projectorBC region)
  calc
    (M.projectorAB region * M.projectorBC region) * M.projectorCD region =
        M.projectorAB region * (M.projectorBC region * M.projectorCD region) := by
          rw [mul_assoc]
    _ = M.projectorAB region * (M.projectorCD region * M.projectorBC region) := by
          rw [(M.projectorBC_commute_projectorCD region).eq]
    _ = (M.projectorAB region * M.projectorCD region) * M.projectorBC region := by
          rw [← mul_assoc]
    _ = (M.projectorCD region * M.projectorAB region) * M.projectorBC region := by
          rw [(M.projectorAB_commute_projectorCD region).eq]
    _ = M.projectorCD region * (M.projectorAB region * M.projectorBC region) := by
          rw [mul_assoc]
end QEC.Bounds.BPTCommutingProjectorModel
