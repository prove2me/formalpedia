-- Prove2me | solution 1 for QEC.Coding.FiberBundle.inSameSupportedHorizontalCluster_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:55:33.241836+00:00
-- url     : https://prove2.me/submissions/c46736cd-be76-4ee9-91c7-68f05ea585ff

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives

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
    (root x y : Fin (4 * r) × ZMod (ell * ell))
    (hxCluster : InSameSupportedHorizontalCluster
      baseSample twistSample z root x)
    (hxSupport : z (Sum.inl x) ≠ 0)
    (hySupport : z (Sum.inl y) ≠ 0)
    (hxy : HorizontalBoundaryOverlap baseSample twistSample x y) :
    InSameSupportedHorizontalCluster
      baseSample twistSample z root y := by
  exact Relation.ReflTransGen.tail hxCluster
    ⟨hxSupport, hySupport, hxy⟩
end QEC.Coding.FiberBundle
