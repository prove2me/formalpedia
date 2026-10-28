-- Prove2me | solution 1 for actuarial_f_compound_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:34:56.523241+00:00
-- url     : https://prove2.me/submissions/cf64ce58-c2e7-465e-af12-79fb04bd2776

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_compoundGrowth

open ActuarialUnderpinsF

theorem solution (r : ℕ → ℝ) (t : ℕ)
    (hr : ∀ k ∈ Finset.range t, -1 ≤ r k) :
    0 ≤ compoundGrowth r t := by
  have pnn : ∀ (s : Finset ℕ) (f : ℕ → ℝ), (∀ x ∈ s, 0 ≤ f x) → 0 ≤ s.prod f := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_nonneg (hf a (Finset.mem_insert_self a s)) (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
  unfold compoundGrowth
  exact pnn _ _ fun k hk => by grind [hr k hk]
