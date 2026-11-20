-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.externalBoundary_disjoint_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:18.303016+00:00
-- url     : https://prove2.me/submissions/82059c05-789b-414e-b049-66e402d3e620

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundary_disjoint_of_actualProjectorSeparated

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
    Disjoint (M.externalBoundary left) right := by
  rw [Finset.disjoint_left]
  intro site hexternal hright
  exact (Finset.disjoint_left.mp
    (M.boundary_disjoint_of_actualProjectorSeparated left right hseparated))
      (Finset.mem_sdiff.mp hexternal).1 hright
end QEC.Bounds.BPTCommutingProjectorModel
