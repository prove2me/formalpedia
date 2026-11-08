-- Prove2me | solution 1 for SteinerNav.observation_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:34:00.010215+00:00
-- url     : https://prove2.me/submissions/6da8de5d-eaf4-4511-aeae-f2734cc9b5f2

import Mathlib
import Definitions.Def_SteinerNav_Covers

open SteinerNav in
theorem solution {d : ℕ} (α : ℝ) (hα : 1 < α) (s s' v t : Pt d) (h : Covers α s v t)
    (hs : dist s t ≤ dist s' t) : Covers α s' v t := by
  unfold Covers at *
  exact lt_of_lt_of_le h (div_le_div_of_nonneg_right hs (by linarith))
