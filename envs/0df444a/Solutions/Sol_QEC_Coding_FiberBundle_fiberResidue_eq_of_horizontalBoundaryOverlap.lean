-- Prove2me | solution 1 for QEC.Coding.FiberBundle.fiberResidue_eq_of_horizontalBoundaryOverlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:06:26.884972+00:00
-- url     : https://prove2.me/submissions/a24f679d-83a2-4023-93ef-82e0b9df74b6

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_fiberResidue_eq_of_connected_horizontal_positions

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
    (hxy : HorizontalBoundaryOverlap baseSample twistSample x y) :
    fiberResidue ell x.2 = fiberResidue ell y.2 := by
  rcases hxy with ⟨a, _hax, _hay, hMeet⟩
  exact fiberResidue_eq_of_connected_horizontal_positions
    baseSample twistSample x.1 y.1 a x.2 y.2 hMeet
end QEC.Coding.FiberBundle
