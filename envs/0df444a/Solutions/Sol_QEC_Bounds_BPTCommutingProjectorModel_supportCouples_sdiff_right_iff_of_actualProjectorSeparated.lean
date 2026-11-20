-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.supportCouples_sdiff_right_iff_of_actualProjectorSeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:04.912856+00:00
-- url     : https://prove2.me/submissions/f0d40882-a9fe-4f54-baa1-11c1b0bb6b47

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_support_disjoint_intersection_of_actualProjectorSeparated

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
    M.supportCouples check (left \ right) ↔ M.supportCouples check left := by
  unfold supportCouples
  have hsupport := M.support_disjoint_intersection_of_actualProjectorSeparated
    left right hseparated check
  constructor
  · rintro ⟨hinside, houtside⟩
    constructor
    · rcases hinside with ⟨site, hsite⟩
      rcases Finset.mem_inter.mp hsite with ⟨hsupportSite, hleftMinus⟩
      exact ⟨site, Finset.mem_inter.mpr ⟨hsupportSite, (Finset.mem_sdiff.mp hleftMinus).1⟩⟩
    · rcases houtside with ⟨site, hsite⟩
      rcases Finset.mem_sdiff.mp hsite with ⟨hsupportSite, hnotLeftMinus⟩
      refine ⟨site, Finset.mem_sdiff.mpr ⟨hsupportSite, ?_⟩⟩
      intro hleft
      by_cases hright : site ∈ right
      · exact (Finset.disjoint_left.mp hsupport) hsupportSite
          (Finset.mem_inter.mpr ⟨hleft, hright⟩)
      · exact hnotLeftMinus (Finset.mem_sdiff.mpr ⟨hleft, hright⟩)
  · rintro ⟨hinside, houtside⟩
    constructor
    · rcases hinside with ⟨site, hsite⟩
      rcases Finset.mem_inter.mp hsite with ⟨hsupportSite, hleft⟩
      refine ⟨site, Finset.mem_inter.mpr ⟨hsupportSite, ?_⟩⟩
      refine Finset.mem_sdiff.mpr ⟨hleft, ?_⟩
      intro hright
      exact (Finset.disjoint_left.mp hsupport) hsupportSite
        (Finset.mem_inter.mpr ⟨hleft, hright⟩)
    · rcases houtside with ⟨site, hsite⟩
      rcases Finset.mem_sdiff.mp hsite with ⟨hsupportSite, hnotLeft⟩
      refine ⟨site, Finset.mem_sdiff.mpr ⟨hsupportSite, ?_⟩⟩
      intro hleftMinus
      exact hnotLeft (Finset.mem_sdiff.mp hleftMinus).1
end QEC.Bounds.BPTCommutingProjectorModel
