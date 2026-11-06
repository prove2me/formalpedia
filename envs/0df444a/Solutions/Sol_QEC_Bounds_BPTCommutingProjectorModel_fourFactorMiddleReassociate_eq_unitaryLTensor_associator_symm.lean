-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorMiddleReassociate_eq_unitaryLTensor_associator_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:26:16.290685+00:00
-- url     : https://prove2.me/submissions/d5716ce0-ef54-4826-b439-c80ee0ef234d

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport

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
    M.fourFactorMiddleReassociate region =
      unitaryLTensor (M.fourFactorA region)
        (tensorAssociatorUnitary (M.fourFactorB region)
          (M.fourFactorC region) (M.fourFactorD region)).symm := by
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
