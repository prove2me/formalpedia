-- Prove2me | solution 1 for PassivityUn.stdJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T21:35:32.910241+00:00
-- url     : https://prove2.me/submissions/f16300b1-b691-4095-93bf-6159f1aeeb65

import Mathlib
import Definitions.Def_PassivityUn_stdJ

open Matrix PassivityUn

theorem solution (n : ℕ) : stdJ n * stdJ n = -1 := by
  simp [stdJ, fromBlocks_multiply]
  rw [← fromBlocks_one, fromBlocks_neg]; simp
