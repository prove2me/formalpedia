-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.boundary_disjoint_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:26.119224+00:00
-- url     : https://prove2.me/submissions/19b600d3-5872-4b53-a565-1b158781234e

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
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
    Disjoint (M.boundary left) right := by
  rw [Finset.disjoint_left]
  intro site hboundary hright
  rcases (M.mem_boundary_iff left site).1 hboundary with
    ⟨check, hcouples, hsite⟩
  apply hseparated check
  refine ⟨?_, ?_⟩
  · exact hcouples.1
  · exact ⟨site, Finset.mem_inter.mpr ⟨hsite, hright⟩⟩
end QEC.Bounds.BPTCommutingProjectorModel
