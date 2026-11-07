-- Prove2me | solution 1 for QEC.Coding.FiberBundle.horizontalBaseLift_add_bundleCoboundary_eraseC0Fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:22:50.959655+00:00
-- url     : https://prove2.me/submissions/6b055fc7-4664-4955-a69f-2ccc91625c33

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_bundleCoboundary_eraseC0Fiber

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
    (x : Word (ZMod 2) baseOne)
    (u : Word (ZMod 2) (C0Index baseZero fiberZero))
    (a : baseZero) :
    horizontalBaseLift
          (baseZero := baseZero) (fiberZero := fiberZero)
          (fiberOne := fiberOne) x +
        bundleCoboundary D (eraseC0Fiber u a) =
      (horizontalBaseLift
            (baseZero := baseZero) (fiberZero := fiberZero)
            (fiberOne := fiberOne) x +
          bundleCoboundary D u) +
        bundleCoboundary D (eraseC0FiberCorrection u a) := by
  rw [bundleCoboundary_eraseC0Fiber]
  exact (add_assoc
    (horizontalBaseLift
      (baseZero := baseZero) (fiberZero := fiberZero)
      (fiberOne := fiberOne) x)
    (bundleCoboundary D u)
    (bundleCoboundary D (eraseC0FiberCorrection u a))).symm
end QEC.Coding.FiberBundle
