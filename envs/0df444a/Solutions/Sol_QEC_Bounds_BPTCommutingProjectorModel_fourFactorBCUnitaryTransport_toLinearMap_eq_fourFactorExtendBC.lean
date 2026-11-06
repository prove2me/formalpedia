-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorBCUnitaryTransport_toLinearMap_eq_fourFactorExtendBC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:36:30.2131+00:00
-- url     : https://prove2.me/submissions/840e997d-a7e0-4b91-a06a-2e022cf27db0

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (E : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))
      (Semantics.CompositeSystem (M.fourFactorB region) (M.fourFactorC region))) :
    (fourFactorBCUnitaryTransport (A := M.fourFactorA region)
      (D := M.fourFactorD region) E).toLinearEquiv.toLinearMap =
      M.fourFactorExtendBC region E.toLinearEquiv.toLinearMap := by
  unfold fourFactorExtendBC
  rw [M.fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm]
  exact fourFactorBCUnitaryTransport_toLinearMap_eq_middleExtension E
end QEC.Bounds.BPTCommutingProjectorModel
