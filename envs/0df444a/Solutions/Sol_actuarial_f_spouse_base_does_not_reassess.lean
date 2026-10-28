-- Prove2me | solution 1 for actuarial_f_spouse_base_does_not_reassess
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:37:44.333002+00:00
-- url     : https://prove2.me/submissions/b1dfb3c3-2393-4e5c-aa11-ff4c2cd3dd3e

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem solution (h z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (hd : spouseDue h i j t = 1) :
    spouseInstalment h z i j t s gs = s z i * gs i t := by
  unfold spouseInstalment
  rw [hd, mul_one]
