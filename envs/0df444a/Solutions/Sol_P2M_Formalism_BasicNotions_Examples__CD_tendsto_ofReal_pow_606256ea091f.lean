-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_tendsto_ofReal_pow_606256ea091f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:49.98381+00:00
-- url     : https://prove2.me/submissions/9d82cba4-7d0a-4929-8999-66f26e7da88f

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (n : ℕ) (σ : ℝ) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + σ * ε) ^ n)) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun ε : ℝ => (1 + σ * ε) ^ n) (𝓝 0) (𝓝 ((1 + σ * 0) ^ n)) :=
    ((tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_id)).pow n)
  rw [mul_zero, add_zero, one_pow] at h
  have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp h
  rw [ENNReal.ofReal_one] at h2
  exact h2.mono_left nhdsWithin_le_nhds
end Formalism.BasicNotions.Examples₂.CD
