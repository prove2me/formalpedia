-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_eq_of_inSameHorizontalCluster
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:09:36.216541+00:00
-- url     : https://prove2.me/submissions/43fcb4c5-2a63-4a48-876c-60a2876c6f30

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_horizontalBoundaryOverlap

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    {x y : Fin (4 * r) × ZMod (ell * ell)}
    (hxy : InSameHorizontalCluster baseSample twistSample x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by
  induction hxy with
  | refl => rfl
  | tail hxy hyz ih =>
      exact ih.trans
        (fiberResidue_eq_of_horizontalBoundaryOverlap
          baseSample twistSample hyz)
end QEC.Coding.FiberBundle
