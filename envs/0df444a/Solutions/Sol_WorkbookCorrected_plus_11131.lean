-- Prove2me | solution 1 for WorkbookCorrected.plus_11131
-- status  : ACCEPTED   (prove)
-- author  : @Sneed
-- created : 2026-09-29T20:25:51.573237+00:00
-- url     : https://prove2.me/submissions/dc2d5bd3-bca0-49a9-b482-ad59455ff93c

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    (286 : ℚ) * (Nat.choose 9 6) =
      (3 : ℚ) * (Nat.choose 16 6) := by
  norm_num [Nat.choose]
