-- Prove2me | solution 1 for actuarial_f_guarantee_first_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:38:01.500051+00:00
-- url     : https://prove2.me/submissions/50332df7-ffab-4981-9f9c-67e4690426eb

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue

open ActuarialUnderpinsF

theorem solution (h r g i t : ℕ)
    (hr : r ≤ i) (hc : i < h) (hi : i < t) (hd : r ≤ t)
    (hg : t < r + g) : estateDue h r g i t = 1 := by
  unfold estateDue
  rw [if_pos ⟨hr, hc, hi, hd, hg⟩]
