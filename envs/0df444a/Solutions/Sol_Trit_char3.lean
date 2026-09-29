-- Prove2me | solution 1 for Trit.char3
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-29T00:38:48.110468+00:00
-- url     : https://prove2.me/submissions/f597624a-09b6-4ba9-a498-b665477a71b4

import Mathlib

theorem solution (x : ZMod 3) : x + x + x = 0 := by
  revert x
  decide
