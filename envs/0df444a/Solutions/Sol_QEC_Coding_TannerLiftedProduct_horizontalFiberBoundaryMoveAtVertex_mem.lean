-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.horizontalFiberBoundaryMoveAtVertex_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:47:42.355326+00:00
-- url     : https://prove2.me/submissions/df141f13-5641-4ac5-9e51-8860dbad333a

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
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (v : VertexIndex G) (a : W) (u : Word F R') :
    horizontalFiberBoundaryMoveAtVertex label h g' v a u ∈
      horizontalFiberBoundaryMoves label h g' := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(horizontalEdgeAtVertex label v a, u), Finset.mem_univ _, rfl⟩
end QEC.Coding.TannerLiftedProduct
