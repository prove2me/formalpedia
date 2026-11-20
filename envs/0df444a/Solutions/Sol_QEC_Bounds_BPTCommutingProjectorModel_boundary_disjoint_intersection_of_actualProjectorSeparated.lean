-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundary_disjoint_intersection_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:08.618568+00:00
-- url     : https://prove2.me/submissions/0e1373fb-73f8-47ce-8132-d765b614ba06

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_support_disjoint_intersection_of_actualProjectorSeparated
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
    Disjoint (M.boundary left) (left ∩ right) := by
  rw [Finset.disjoint_left]
  intro site hboundary hintersection
  rcases (M.mem_boundary_iff left site).mp hboundary with ⟨check, _, hsupport⟩
  exact (Finset.disjoint_left.mp
    (M.support_disjoint_intersection_of_actualProjectorSeparated left right hseparated check))
      hsupport hintersection
end QEC.Bounds.BPTCommutingProjectorModel
