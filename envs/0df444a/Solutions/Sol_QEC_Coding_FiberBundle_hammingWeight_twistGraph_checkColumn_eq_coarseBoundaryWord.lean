-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_twistGraph_checkColumn_eq_coarseBoundaryWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:07:17.793019+00:00
-- url     : https://prove2.me/submissions/f4f19824-4f0e-4751-b2a9-1c92753fcbb8

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_twistGraph_checkSyndrome_eq_horizontalChainBoundary
import Theorems.Thm_QEC_Coding_FiberBundle_horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_reindexWord


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (z : Word (ZMod 2)
      (QubitIndex (Fin (3 * r)) (Fin (4 * r))
        (ZMod (ell * ell)) (ZMod (ell * ell))))
    (hz :
      z ∈ (chainComplex
        (RandomTwist.fiberBundleData baseSample twistSample)
        ).middleCycleCode.carrier)
    (a : Fin (3 * r)) :
    HammingWeight
        (TwistGraph.checkColumn baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) a) =
      HammingWeight (coarseBoundaryWord ell (verticalFiber z a)) := by
  let e : ZMod ell ≃ ZMod ell :=
    (TwistGraph.typeTranslation twistSample
      (RandomTwist.checkType typeCount a)).symm
  have hWord :
      TwistGraph.checkColumn baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) a =
        reindexWord e
          (coarseBoundaryWord ell (verticalFiber z a)) := by
    funext u
    change
      TwistGraph.checkSyndrome baseSample twistSample
          (twistGraphWordOfHorizontalComponent z) u a =
        cycleFiberChainBoundary (ell * ell) (verticalFiber z a)
          (TwistGraph.layerEmbedding ell
            (TwistGraph.outNeighbor twistSample
              (RandomTwist.checkType typeCount a) u))
    rw [twistGraph_checkSyndrome_eq_horizontalChainBoundary]
    exact congrFun
      (horizontalChainBoundary_horizontalComponent_eq_cycleFiberChainBoundary
        baseSample twistSample z hz a) _
  rw [hWord]
  exact hammingWeight_reindexWord e
    (coarseBoundaryWord ell (verticalFiber z a))
end QEC.Coding.FiberBundle
