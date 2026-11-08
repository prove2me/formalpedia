-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.mem_faceStar_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:39:38.063569+00:00
-- url     : https://prove2.me/submissions/a20330de-a593-43cc-be24-82d6418a59aa

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
theorem _root_.solution (label : W → G) (v : VertexIndex G)
    (p : FaceIndex W G) :
    p ∈ faceStar label v ↔ ∃ a b, faceAtVertex label v a b = p := by
  classical
  constructor
  · intro hp
    obtain ⟨q, _hq, hq⟩ := Finset.mem_map.mp hp
    exact ⟨q.2, q.1, hq⟩
  · rintro ⟨a, b, rfl⟩
    exact Finset.mem_map.mpr ⟨(b, a), Finset.mem_univ _, rfl⟩
end QEC.Coding.TannerLiftedProduct
