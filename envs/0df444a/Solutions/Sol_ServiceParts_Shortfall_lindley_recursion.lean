-- Prove2me | solution 1 for ServiceParts.Shortfall.lindley_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:19:13.782878+00:00
-- url     : https://prove2.me/submissions/a2f1989c-a00a-4d32-8d91-de246f257186

import Mathlib
import Definitions.Def_ServiceParts_Shortfall_ShortfallModel

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

open MeasureTheory ProbabilityTheory ServiceParts.Shortfall in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ShortfallModel Ω P) (s : ℝ) (n : ℕ) (ω : Ω) :
    s - M.netInventory s n ω = M.shortfall n ω := by
  induction n with
  | zero => simp [ShortfallModel.netInventory, ShortfallModel.shortfall]
  | succ k ih =>
    simp only [ShortfallModel.netInventory, ShortfallModel.shortfall]
    rw [← ih]
    rcases le_total M.capacity (s - M.netInventory s k ω + M.demand (k + 1) ω) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
