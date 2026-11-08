-- Prove2me | solution 1 for StaticCalendar.binary_assumption2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:21:38.627867+00:00
-- url     : https://prove2.me/submissions/28fcab33-fe08-4cdb-8fb6-2f6d4d007a9f

import Mathlib
import Definitions.Def_StaticCalendar_Assumption2
import Definitions.Def_StaticCalendar_BinaryDemand

open MeasureTheory

open StaticCalendar in
theorem solution {n m : ℕ} (I : DemandModel n m) (h : BinaryDemand I) :
    Assumption2 I := by
  intro i S hS S' hS' j j' _ c hc
  have key : ∀ T ∈ I.family, ∀ k, ∫ Q, min c (Q (i, k)) ∂I.D T = c * I.q T i k := by
    intro T hT k
    unfold DemandModel.q
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [h T hT] with Q hQ
    rcases hQ (i, k) with h0 | h1
    · rw [h0, min_eq_right hc.1, mul_zero]
    · rw [h1, min_eq_left hc.2, mul_one]
  rw [key S' hS' j', key S hS j]
  exact le_of_eq (by ring)
