-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.neighborEdgeCount_mono_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:47:34.157119+00:00
-- url     : https://prove2.me/submissions/6daf67e3-0a87-4fc5-aa82-2aef9ce62287

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphMixing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero ell]
    (twistSample : RandomTwist.Sample r typeCount ell)
    (source₁ source₂ target : Finset (ZMod ell))
    (hsubset : source₁ ⊆ source₂) :
    neighborEdgeCount twistSample source₁ target ≤
      neighborEdgeCount twistSample source₂ target := by
  exact Finset.sum_le_sum_of_subset hsubset
end QEC.Coding.FiberBundle.TwistGraph
