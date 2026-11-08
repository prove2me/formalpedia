-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.mem_horizontalFaceColumn_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:38:10.436892+00:00
-- url     : https://prove2.me/submissions/733aa0e4-7ab2-436a-8808-4ada5c129b81

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Field F] [Fintype F] [DecidableEq F] [Fintype G]
    [DecidableEq G] [DecidableEq W] [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (v : VertexIndex G) (a : W) (p : FaceIndex W G) :
    p ∈ horizontalFaceColumn label v a ↔
      ∃ b, faceAtVertex label v a b = p := by
  classical
  constructor
  · intro hp
    obtain ⟨b, _hb, hbp⟩ := Finset.mem_map.mp hp
    exact ⟨b, hbp⟩
  · rintro ⟨b, rfl⟩
    exact Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩
end QEC.Coding.TannerLiftedProduct
