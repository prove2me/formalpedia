-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_codeSpace_carrier_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:06:43.810806+00:00
-- url     : https://prove2.me/submissions/1d16bc1c-5b45-4767-ac14-67e089970172

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_exists_erasureRecovery
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_of_carrier_eq_bot


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
    (hcode : M.codeSpace.carrier = ⊥) :
    M.RegionErasureRecoverable region := by
  apply ((M.regionSubsystem region).noInformationOn_iff_exists_erasureRecovery
    M.codeSpace L.localDimension_positive).mp
  exact Semantics.QuditSubsystem.noInformationOn_of_carrier_eq_bot
    M.codeSpace (M.regionSubsystem region) hcode
end QEC.Bounds.BPTCommutingProjectorModel
