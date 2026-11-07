-- Prove2me | solution 1 for QEC.Coding.FiberBundle.exists_boundary2_eq_verticalFundamentalWord_of_fullRowRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:56:42.746996+00:00
-- url     : https://prove2.me/submissions/5cfdb310-ceab-4be9-b584-223a355557f6

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_boundary2_constantFiberTwoChain_eq_verticalFundamentalWord

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : RandomTwist.Sample r typeCount ell)
    (hRank : RandomBase.HasFullRowRank baseSample)
    (y : Word (ZMod 2) (Fin (3 * r))) :
    ∃ c : Word (ZMod 2)
        (C2Index (Fin (4 * r)) (ZMod (ell * ell))),
      boundary2
          (RandomTwist.fiberBundleData baseSample twistSample) c =
        verticalFundamentalWord
          (baseOne := Fin (4 * r))
          (fiberZero := ZMod (ell * ell))
          (fiberOne := ZMod (ell * ell)) y := by
  rcases hRank y with ⟨x, hx⟩
  refine ⟨constantFiberTwoChain
    (fiberOne := ZMod (ell * ell)) x, ?_⟩
  rw [boundary2_constantFiberTwoChain_eq_verticalFundamentalWord]
  rw [hx]
end QEC.Coding.FiberBundle
