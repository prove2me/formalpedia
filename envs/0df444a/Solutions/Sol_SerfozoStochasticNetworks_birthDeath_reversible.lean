-- Prove2me | solution 1 for SerfozoStochasticNetworks.birthDeath_reversible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:32.6226+00:00
-- url     : https://prove2.me/submissions/78758844-0bfd-4c95-820b-6755b2816812

import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

end SerfozoStochasticNetworks

open SerfozoStochasticNetworks
theorem solution (lam mu : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (hmu : ∀ n, 0 < mu (n + 1)) :
    DetailedBalance (birthDeathRate lam mu) (birthDeathMeasure lam mu) ∧
      IsReversible (birthDeathRate lam mu) := by
  have hπpos : ∀ x, 0 < birthDeathMeasure lam mu x := by
    intro x
    unfold birthDeathMeasure
    apply Finset.prod_pos
    intro n _
    exact div_pos (hlam n) (hmu n)
  have hstep : ∀ x, birthDeathMeasure lam mu (x + 1) * mu (x + 1)
      = birthDeathMeasure lam mu x * lam x := by
    intro x
    unfold birthDeathMeasure
    rw [Finset.prod_range_succ, mul_assoc, div_mul_cancel₀ _ (hmu x).ne']
  have hdb : DetailedBalance (birthDeathRate lam mu) (birthDeathMeasure lam mu) := by
    intro x y
    unfold birthDeathRate
    split_ifs with hxy hyx hyx
    · omega
    · subst hxy
      exact (hstep x).symm
    · subst hyx
      exact hstep y
    · ring
  exact ⟨hdb, birthDeathMeasure lam mu, hπpos, hdb⟩

