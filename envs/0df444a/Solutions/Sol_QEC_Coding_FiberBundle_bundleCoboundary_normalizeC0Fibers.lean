-- Prove2me | solution 1 for QEC.Coding.FiberBundle.bundleCoboundary_normalizeC0Fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:17.880165+00:00
-- url     : https://prove2.me/submissions/bd25b026-e62d-4f06-a032-6f97538fca74

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_normalizeC0Fibers_eq_add_normalizationToggleWord

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
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    bundleCoboundary D (normalizeC0Fibers u) =
      bundleCoboundary D u +
        bundleCoboundary D (normalizationToggleWord u) := by
  rw [normalizeC0Fibers_eq_add_normalizationToggleWord]
  exact map_add (wordLinearMapTranspose (boundary1 D)) u
    (normalizationToggleWord u)
end QEC.Coding.FiberBundle
