-- Prove2me | solution 1 for QEC.Coding.FiberBundle.TwistGraph.checkSyndrome_eq_pairCheckSyndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:47:28.432532+00:00
-- url     : https://prove2.me/submissions/19350b29-e816-4911-9318-2b7d526f8180

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphLTC

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators
namespace QEC.Coding.FiberBundle.TwistGraph
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (w : Word (ZMod 2) (ZMod ell × Fin (4 * r)))
    (u : ZMod ell) (a : Fin (3 * r)) :
    checkSyndrome baseSample twistSample w u a =
      pairCheckSyndrome baseSample twistSample
        (layerWord w u)
        (layerWord w
          (outNeighbor twistSample
            (RandomTwist.checkType typeCount a) u))
        a := by
  rfl
end QEC.Coding.FiberBundle.TwistGraph
