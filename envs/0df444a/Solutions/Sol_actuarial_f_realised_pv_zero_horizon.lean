-- Prove2me | solution 1 for actuarial_f_realised_pv_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:39:54.64834+00:00
-- url     : https://prove2.me/submissions/4eca518b-0b84-4817-9806-e7d9afe7b735

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_realisedPV

open ActuarialUnderpinsF

theorem solution (r g z i j : ℕ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (ge : ℕ → ℝ) (hr : 0 < r) :
    realisedPV 0 r g z i j disc a b c s estate g0 g1 gs ge = 0 := by
  have hr' : ¬ r ≤ 0 := by omega
  simp [realisedPV, totalInstalment, memberTrancheOne, memberTrancheTwo, spouseInstalment,
    estateInstalment, memberDue, spouseDue, estateDue, hr']
