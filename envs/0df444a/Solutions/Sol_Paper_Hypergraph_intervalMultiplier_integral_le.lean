-- Prove2me | solution 1 for Paper.Hypergraph.intervalMultiplier_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:18:57.982801+00:00
-- url     : https://prove2.me/submissions/0cee797a-5552-435a-9023-dc38413f4566

import Definitions.Def_Paper_TwoTerminalRounding
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Paper_RoundingAveraging
import Theorems.Thm_Paper_Hypergraph_integral_le_one_add_two_log
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_measurable
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_nonneg
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_le
import Theorems.Thm_Paper_Hypergraph_intervalMultiplier_tail

set_option autoImplicit true
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open Paper Paper.Hypergraph
namespace Paper.Hypergraph
theorem _root_.solution {V : Finset ℕ} (hne : V.Nonempty) {x d : ℕ → ℝ}
    {ε q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hx : ∀ v ∈ V, x v = 0 ∨ ε ≤ x v)
    (hq : ∀ v ∈ V, d v - x v ≤ q ∧ q ≤ d v) :
    ∫ r, intervalMultiplier V hne x d r ∂levelMeasure ≤ 1 + 2 * Real.log (1 / ε) := by
  apply integral_le_one_add_two_log (intervalMultiplier_measurable V hne x d)
    (intervalMultiplier_nonneg hne (fun v hv => by rcases hx v hv with h | h <;> linarith))
    ((le_div_iff₀ hε).2 (by simpa using hε1)) (intervalMultiplier_le hne hε hx)
  intro t ht
  exact intervalMultiplier_tail hne hq (by linarith)
end Paper.Hypergraph
