-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_eq_of_inSameSupportedHorizontalCluster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:12:52.380734+00:00
-- url     : https://prove2.me/submissions/68688e66-bc44-4be1-99ef-1f3421b186ec

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_inSameHorizontalCluster

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
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : InSameSupportedHorizontalCluster
      baseSample twistSample z x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by
  apply fiberResidue_eq_of_inSameHorizontalCluster
    baseSample twistSample
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih hyz.2.2
end QEC.Coding.FiberBundle
