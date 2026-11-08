-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.unlabelledActiveVerticalEdges_subset_activeVerticalEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:12:19.513694+00:00
-- url     : https://prove2.me/submissions/54dc9e03-fa94-44fc-a2dd-79ed66706a0a

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerGlobalExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLabelledEdges

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
omit [Fintype F] [DecidableEq W] [DecidableEq R] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G)
    (c : Word F
      (LiftedProduct.QubitIndex (Fin 2 × R) W W (Fin 2 × R') G))
    (L : Finset (VertexIndex G)) :
    unlabelledActiveVerticalEdges label c L ⊆ activeVerticalEdges label c := by
  intro e he
  exact (Finset.mem_filter.mp he).1
end QEC.Coding.TannerLiftedProduct
