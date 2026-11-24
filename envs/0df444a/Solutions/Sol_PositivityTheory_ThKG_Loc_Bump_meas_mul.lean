-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.meas_mul
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:56:11.856511+00:00
-- url     : https://prove2.me/submissions/de6b05bc-0f26-4539-9ac1-59a2f8847ca2

import Mathlib
variable {ι : Type} [Fintype ι]


theorem solution (y : ι → ℂ) : Measurable fun x : ι → ℂ => y * x := by
  exact measurable_const.mul measurable_id
