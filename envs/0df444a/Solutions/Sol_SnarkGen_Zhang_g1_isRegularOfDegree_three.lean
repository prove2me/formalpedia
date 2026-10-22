-- Prove2me | solution 1 for SnarkGen.Zhang.g1_isRegularOfDegree_three
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:39:51.235223+00:00
-- url     : https://prove2.me/submissions/dcd83b8a-52d5-4f3e-b5b4-41721186e5f8

import Mathlib
import Definitions.Def_SnarkGen_Zhang_g1

set_option autoImplicit false
open SnarkGen.Zhang

theorem solution : g1.IsRegularOfDegree 3 := by
  intro v
  revert v
  decide +kernel
