-- Prove2me | solution 1 for QEC.Coding.FiberBundle.hammingWeight_horizontalComponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:49:54.309603+00:00
-- url     : https://prove2.me/submissions/c120bc70-aae2-4042-8d59-293796bbbd27

import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_TwistGraph
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Theorems.Thm_QEC_Coding_FiberBundle_hammingWeight_eq_horizontal_add_vertical


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
universe u
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {baseZero baseOne fiberZero fiberOne : Type u}
    [Fintype baseZero] [Fintype baseOne]
    [Fintype fiberZero] [Fintype fiberOne]
    (z : Word (ZMod 2)
      (QubitIndex baseZero baseOne fiberZero fiberOne)) :
    HammingWeight (horizontalComponent z) ≤ HammingWeight z := by
  rw [hammingWeight_eq_horizontal_add_vertical]
  omega
end QEC.Coding.FiberBundle
