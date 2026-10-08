-- Prove2me | solution 3 for PiIrrationality.rhin_viola_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T06:51:38.793766+00:00
-- url     : https://prove2.me/submissions/0ed3c6da-5bcb-4845-af35-c94aaa2a7334
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_PiIrrationality_UpperBound
import Theorems.Thm_RhinViola_zetaTwoIrrationalityBound
import Theorems.Thm_RhinViola_zetaTwoBound_implies_piBound
import Mathlib.Tactic.NormNum

theorem solution :
    PiIrrationality.UpperBound (14.797074 : ℝ) := by
  have h : PiIrrationality.UpperBound (2 * ((7398537 : ℝ) / 1000000)) :=
    RhinViola.zetaTwoBound_implies_piBound
      ((7398537 : ℝ) / 1000000) (by norm_num)
      RhinViola.zetaTwoIrrationalityBound
  convert h using 1 <;> norm_num
