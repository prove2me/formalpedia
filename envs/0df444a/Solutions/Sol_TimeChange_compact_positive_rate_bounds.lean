-- Prove2me | solution 1 for TimeChange.compact_positive_rate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T14:58:09.952532+00:00
-- url     : https://prove2.me/submissions/965ae40f-e086-407e-9f3a-c44bb117f564

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
open Set
open scoped Topology ContDiff
set_option maxHeartbeats 800000

theorem solution {S : Type*} [TopologicalSpace S]
    (K : Set S) (hK : IsCompact K) (hne : K.Nonempty)
    (r : S → ℝ) (hr : ContinuousOn r K) (hpos : ∀ x ∈ K, 0 < r x) :
    ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ K, m ≤ r x ∧ r x ≤ M := by
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hr
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hne hr
  exact ⟨r a, r b, hpos a ha, fun x hx => ⟨hmin hx, hmax hx⟩⟩
