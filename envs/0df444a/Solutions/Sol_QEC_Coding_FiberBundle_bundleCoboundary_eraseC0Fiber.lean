-- Prove2me | solution 1 for QEC.Coding.FiberBundle.bundleCoboundary_eraseC0Fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:19:50.93145+00:00
-- url     : https://prove2.me/submissions/4118c598-dc0f-499a-9025-305cc089209a

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [DecidableEq baseZero]
    [Fintype baseOne] [DecidableEq baseOne]
    [Fintype fiberZero] [DecidableEq fiberZero]
    [Fintype fiberOne] [DecidableEq fiberOne]
    (D : Data baseZero baseOne fiberZero fiberOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    bundleCoboundary D (eraseC0Fiber u a) =
      bundleCoboundary D u +
        bundleCoboundary D (eraseC0FiberCorrection u a) := by
  rw [eraseC0Fiber]
  exact map_add (wordLinearMapTranspose (boundary1 D)) u
    (eraseC0FiberCorrection u a)
end QEC.Coding.FiberBundle
