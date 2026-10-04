-- Prove2me | solution 1 for TimeChange.compact_positive_time_change_flow
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T17:00:46.407062+00:00
-- url     : https://prove2.me/submissions/f94eb301-cecb-4b39-aa5a-9d7e401ea6ef

import Mathlib.Dynamics.Flow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring
import Theorems.Thm_TimeChange_compact_positive_rate_bounds
import Theorems.Thm_TimeChange_positive_time_change_flow
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem solution {S : Type*} [TopologicalSpace S] [CompactSpace S]
    (flow : Flow ℝ S) (r : S → ℝ) (hr : Continuous r) (hpos : ∀ s, 0 < r s) :
    ∃ c : S → (ℝ ≃o ℝ), ∃ newFlow : Flow ℝ S,
      (∀ s, c s 0 = 0) ∧
      (∀ s t, HasDerivAt (c s) (r (flow t s)) t) ∧
      (∀ t s, newFlow t s = flow ((c s).symm t) s) ∧
      (∀ s a b, c s (a + b) = c s b + c (flow b s) a) ∧
      Continuous (fun p : ℝ × S => c p.2 p.1) := by
  classical
  have hb : ∃ m : ℝ, 0 < m ∧ ∀ s, m ≤ r s := by
    by_cases hne : Nonempty S
    · obtain ⟨s⟩ := hne
      obtain ⟨m, _, hm, h⟩ := TimeChange.compact_positive_rate_bounds univ isCompact_univ
        ⟨s, mem_univ s⟩ r hr.continuousOn (fun s _ => hpos s)
      exact ⟨m, hm, fun s => (h s (mem_univ s)).1⟩
    · exact ⟨1, by norm_num, fun s => False.elim (hne ⟨s⟩)⟩
  obtain ⟨m, hm, hb⟩ := hb
  exact TimeChange.positive_time_change_flow flow r hr m hm hb
