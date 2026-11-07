-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.hasHHO20LayerMixing_of_edgeMixing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:33.76547+00:00
-- url     : https://prove2.me/submissions/5b311fb6-a52c-4c13-b0e5-442484c997b5

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_layer_cardinality_bounds_of_small
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_badNonheavy_card_bound_of_upperEdgeMixing
import Theorems.Thm_QEC_Coding_FiberBundle_TwistGraph_usableHeavy_card_bound_of_lowerEdgeMixing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero r] [NeZero typeCount] [NeZero ell]
    (Delta : Nat)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hEdge : HasHHO20EdgeMixing Delta twistSample) :
    HasHHO20LayerMixing Delta twistSample := by
  intro w hsmall
  have hcards := layer_cardinality_bounds_of_small Delta w hsmall
  have hmixed := hEdge w hcards.1 hcards.2
  refine ⟨
    badNonheavy_card_bound_of_upperEdgeMixing
      Delta twistSample w hmixed.1, ?_⟩
  intro hcase
  exact usableHeavy_card_bound_of_lowerEdgeMixing
    Delta twistSample w (hmixed.2 hcase)
end QEC.Coding.FiberBundle.TwistGraph
