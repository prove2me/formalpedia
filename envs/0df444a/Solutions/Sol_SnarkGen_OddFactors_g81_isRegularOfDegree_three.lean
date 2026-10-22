-- Prove2me | solution 1 for SnarkGen.OddFactors.g81_isRegularOfDegree_three
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:25:03.981597+00:00
-- url     : https://prove2.me/submissions/461cc4bf-627a-45e7-be1c-627c2204002e

import Mathlib
import Definitions.Def_SnarkGen_OddFactors_G81

set_option autoImplicit false
open SnarkGen.OddFactors

theorem solution : G81.IsRegularOfDegree 3 := by
  intro v
  revert v
  decide +kernel
