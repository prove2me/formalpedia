-- Prove2me | solution 1 for QEC.Coding.FiberBundle.inSameHorizontalCluster_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:02:15.340238+00:00
-- url     : https://prove2.me/submissions/1098088d-61fa-46d6-a2ee-a2fa3d021126

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
    (twistSample : RandomTwist.Sample r typeCount ell) :
    Symmetric (InSameHorizontalCluster baseSample twistSample) := by
  letI : Std.Symm (HorizontalBoundaryOverlap baseSample twistSample) :=
    ⟨fun _ _ h => horizontalBoundaryOverlap_symmetric baseSample twistSample h⟩
  exact fun _ _ h => Relation.ReflTransGen.stdSymm.symm _ _ h
end QEC.Coding.FiberBundle
