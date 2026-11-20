-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.support_disjoint_intersection_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:02.316365+00:00
-- url     : https://prove2.me/submissions/34d0dec8-2ea0-4952-a937-d097507df51f

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation

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
    (hseparated : M.ActualProjectorSeparated left right) (check : kappa) :
    Disjoint (M.support check) (left ∩ right) := by
  rw [Finset.disjoint_left]
  intro site hsupport hintersection
  apply hseparated check
  refine ⟨?_, ?_⟩
  · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_inter.mp hintersection).1⟩⟩
  · exact ⟨site, Finset.mem_inter.mpr ⟨hsupport, (Finset.mem_inter.mp hintersection).2⟩⟩
end QEC.Bounds.BPTCommutingProjectorModel
