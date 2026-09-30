-- Prove2me | solution 1 for RobustLP.Counterpart.star_iff_exists_irc
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:25:54.094835+00:00
-- url     : https://prove2.me/submissions/fc6c9253-1614-4d78-8204-74d03c6d8d45

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts
open scoped BigOperators

namespace RobustLP.Counterpart

/-- **(∗) is equivalent to (IRC[ε, δ])** (Ben-Tal–Nemirovski 2000, §3.1, pp. 417–418). For `ε > 0`
and `δ > 0`, `x` is feasible for (∗) if and only if there is `y` with `(x, y)` feasible for the
interval robust counterpart (IRC[ε, δ]). (Both problems minimize the same objective `cᵀx`.) -/
theorem _root_.solution {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (x : Fin n → ℝ) :
    L.StarFeasible ε δ x ↔ ∃ y : Fin n → ℝ, L.IRCFeasible ε δ x y := by
  constructor
  · rintro ⟨hE, hA, hb, hbox⟩
    refine ⟨fun j => |x j|, hE, hA, hb, ?_, hbox⟩
    exact fun j => ⟨neg_abs_le _, le_abs_self _⟩
  · rintro ⟨y, hE, hA, hb, hy, hbox⟩
    refine ⟨hE, hA, ?_, hbox⟩
    intro i
    have hsum : ∑ j ∈ L.J i, |L.A i j| * |x j| ≤ ∑ j ∈ L.J i, |L.A i j| * y j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (abs_le.mpr (hy j)) (abs_nonneg _)
    have hh := mul_le_mul_of_nonneg_left hsum hε.le
    linarith [hb i]

end RobustLP.Counterpart
