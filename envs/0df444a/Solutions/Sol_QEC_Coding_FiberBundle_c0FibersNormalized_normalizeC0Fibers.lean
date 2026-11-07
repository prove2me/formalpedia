-- Prove2me | solution 1 for QEC.Coding.FiberBundle.c0FibersNormalized_normalizeC0Fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:30:58.851324+00:00
-- url     : https://prove2.me/submissions/4d34169c-0cac-4bf8-a884-844cb00b0f97

import Definitions.Def_QEC_Coding_FiberBundle_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyDistance
import Theorems.Thm_QEC_Coding_FiberBundle_twice_hammingWeight_normalizeC0Fibers_le_card

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero fiberZero : Type u}
    [Fintype fiberZero]
    (u : Word (ZMod 2) (C0Index baseZero fiberZero)) :
    C0FibersNormalized (normalizeC0Fibers u) := by
  intro a
  exact twice_hammingWeight_normalizeC0Fibers_le_card u a
end QEC.Coding.FiberBundle
