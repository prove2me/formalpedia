-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:22:02.373195+00:00
-- url     : https://prove2.me/submissions/55ceeaed-da0f-4411-aea1-e1a73466c9e7

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFaceGraph_external_degree_le_endpoint_adjacency
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_unlabelledActiveVerticalEdges_eq_empty_of_neighborBound

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
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (hcCycle : LiftedProduct.boundary1 (data label h g') c = 0)
    (d m radius : Nat) (lambda : ℝ)
    (hDistance : ∀ x : Word F W,
      x ∈ (ProductExpansion.parityCheckCode h).carrier → x ≠ 0 →
      d ≤ HammingWeight x)
    (L : Finset (VertexIndex G))
    (hClosed : IsClosedLabelledSet label c m L)
    (hExpand : SmallSetExpansion.IsSmallSetEdgeExpanding
      (verticalFaceGraph label) radius lambda)
    (hActiveRadius : (activeVerticalEdges label c).card ≤ radius)
    (hThreshold : (2 * m : ℝ) + lambda ≤ d) :
    unlabelledActiveVerticalEdges label c L = ∅ := by
  apply unlabelledActiveVerticalEdges_eq_empty_of_neighborBound
    label h g' c hcCycle d m radius lambda hDistance L hClosed
    hExpand hActiveRadius
  · intro e _he
    exact verticalFaceGraph_external_degree_le_endpoint_adjacency label c L e
  · exact hThreshold
end QEC.Coding.TannerLiftedProduct
