-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.union_externalBoundary_disjoint_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:15.170511+00:00
-- url     : https://prove2.me/submissions/b29f82c3-c40e-4b8d-967c-f22833e3017c

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_externalBoundary_disjoint_of_actualProjectorSeparated

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
    Disjoint (left ∪ M.externalBoundary left) right := by
  rw [Finset.disjoint_union_left]
  exact ⟨hdisjoint, M.externalBoundary_disjoint_of_actualProjectorSeparated
    left right hseparated⟩
end QEC.Bounds.BPTCommutingProjectorModel
