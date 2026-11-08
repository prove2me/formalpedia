-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.neighborGraph_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:04:18.292773+00:00
-- url     : https://prove2.me/submissions/f85d3506-cdc3-4dcb-b789-e31874ba0e59

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Definitions.Def_QEC_Coding_ExpanderCodes_SmallSetExpansionSquare
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGraphExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe v
variable {G W : Type v}
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {X A : Type*} [Fintype A] [DecidableEq X]
    (neighbor : X → A → X)
    (hInvolution : ∀ x a, neighbor (neighbor x a) a = x) :
    SmallSetExpansion.IsSymmetric
      (fun x y => (Finset.univ.filter fun a => neighbor x a = y).card) := by
  intro x y
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro a _ha
  constructor
  · intro hxy
    rw [← hxy, hInvolution]
  · intro hyx
    rw [← hyx, hInvolution]
end QEC.Coding.TannerLiftedProduct
