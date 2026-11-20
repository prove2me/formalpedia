-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.subset_exterior_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:45:26.039173+00:00
-- url     : https://prove2.me/submissions/62576af6-df5a-4959-9620-7e6b8dfccdf5

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_union_externalBoundary_disjoint_of_actualProjectorSeparated

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
    (hseparated : M.ActualProjectorSeparated left right)
    (hdisjoint : Disjoint left right) :
    right ⊆ M.exterior left := by
  intro site hright
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · apply Finset.mem_compl.mpr
    intro hleft
    exact (Finset.disjoint_left.mp hdisjoint) hleft hright
  · intro hexternal
    exact (Finset.disjoint_left.mp
      (M.union_externalBoundary_disjoint_of_actualProjectorSeparated left right hseparated hdisjoint))
      (Finset.mem_union_right _ hexternal) hright
end QEC.Bounds.BPTCommutingProjectorModel
