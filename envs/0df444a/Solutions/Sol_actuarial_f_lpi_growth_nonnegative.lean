-- Prove2me | solution 1 for actuarial_f_lpi_growth_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:40:06.722882+00:00
-- url     : https://prove2.me/submissions/8b41200b-4e4a-46f7-b462-bdb3d69b5dcd

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiGrowth

open ActuarialUnderpinsF

theorem solution (floor cap : ℝ)
    (inflation : ℕ → ℝ) (t : ℕ)
    (hf : 0 ≤ floor) (hfc : floor ≤ cap) :
    0 ≤ lpiGrowth floor cap inflation t := by
  have pnn : ∀ (s : Finset ℕ) (f : ℕ → ℝ), (∀ x ∈ s, 0 ≤ f x) → 0 ≤ s.prod f := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_nonneg (hf a (Finset.mem_insert_self a s)) (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
  unfold lpiGrowth compoundGrowth lpiPath
  refine pnn _ _ fun k _ => ?_
  have := le_min (le_trans hf hfc) (le_trans hf (le_max_left floor (inflation k)))
  unfold lpiRate
  grind
