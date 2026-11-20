-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundary_sdiff_right_eq_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:11.97018+00:00
-- url     : https://prove2.me/submissions/fbd9829b-278c-42db-ac11-bc08dea99eac

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_supportCouples_sdiff_right_iff_of_actualProjectorSeparated
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_boundary_iff


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
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    (hseparated : M.ActualProjectorSeparated left right) :
    M.boundary (left \ right) = M.boundary left := by
  ext site
  constructor
  · intro hboundary
    rcases (M.mem_boundary_iff (left \ right) site).mp hboundary with
      ⟨check, hcouples, hsupport⟩
    exact (M.mem_boundary_iff left site).mpr ⟨check,
      (M.supportCouples_sdiff_right_iff_of_actualProjectorSeparated left right
        hseparated check).mp hcouples, hsupport⟩
  · intro hboundary
    rcases (M.mem_boundary_iff left site).mp hboundary with ⟨check, hcouples, hsupport⟩
    exact (M.mem_boundary_iff (left \ right) site).mpr ⟨check,
      (M.supportCouples_sdiff_right_iff_of_actualProjectorSeparated left right
        hseparated check).mpr hcouples, hsupport⟩
end QEC.Bounds.BPTCommutingProjectorModel
