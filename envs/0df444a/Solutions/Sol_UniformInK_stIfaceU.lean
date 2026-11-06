-- Prove2me | solution 1 for UniformInK.stIfaceU
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T22:21:10.159295+00:00
-- url     : https://prove2.me/submissions/1b3b888c-88f4-4afa-b527-3df018c38cdd

import Theorems.Thm_UniformInK_ifaceU
import Theorems.Thm_UniformInK_stNodeRootU
import Theorems.Thm_UniformInK_stNodeStepU
import Theorems.Thm_UniformInK_stNodeBoundU
import Theorems.Thm_UniformInK_stThrU
import Theorems.Thm_UniformInK_stBetaSumU

set_option autoImplicit false

section
section

open UniformInK

theorem solution : StIfaceU :=
  ifaceU stNodeRootU stNodeStepU stNodeBoundU stThrU stBetaSumU
