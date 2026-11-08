-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.blockSupportToHammingSupport_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:41.284026+00:00
-- url     : https://prove2.me/submissions/06694c7f-c079-412a-b820-3b94e010cbc6

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
omit [Fintype F] [Group G] [DecidableEq G] [DecidableEq W]
    [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G)) :
    Function.Injective (blockSupportToHammingSupport c) := by
  classical
  intro x y hxy
  cases x with
  | inl p =>
      cases y with
      | inl q =>
          apply congrArg Sum.inl
          apply Subtype.ext
          have hcoord := congrArg Subtype.val hxy
          exact Sum.inl.inj hcoord
      | inr q =>
          have hcoord := congrArg Subtype.val hxy
          cases hcoord
  | inr p =>
      cases y with
      | inl q =>
          have hcoord := congrArg Subtype.val hxy
          cases hcoord
      | inr q =>
          apply congrArg Sum.inr
          apply Subtype.ext
          have hcoord := congrArg Subtype.val hxy
          have hVertex := congrArg
            (coordinateVertex (R := R) (R' := R')) hcoord
          exact Option.some.inj hVertex
end QEC.Coding.TannerLiftedProduct
