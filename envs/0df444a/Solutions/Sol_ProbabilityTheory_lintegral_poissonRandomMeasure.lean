-- Prove2me | solution 1 for ProbabilityTheory.lintegral_poissonRandomMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:39:20.519186+00:00
-- url     : https://prove2.me/submissions/3ffb19cb-093a-4899-b7f8-0de2bf04a48d

import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

theorem solution :
    ∀ {Ω E : Type} [MeasurableSpace E]
      {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {g : E → ℝ≥0∞},
      Measurable g → ∀ (ω : Ω),
        ∫⁻ x, g x ∂(poissonRandomMeasure K X ω)
          = ∑' k, ∑ n ∈ Finset.range (K k ω), g (X k n ω) := by
  intro Ω E _ K X g hg ω
  rw [poissonRandomMeasure, lintegral_sum_measure]
  refine tsum_congr fun k => ?_
  rw [lintegral_sum_measure]
  have hterm : ∀ n, ∫⁻ x, g x ∂(if n < K k ω then Measure.dirac (X k n ω) else 0)
      = if n < K k ω then g (X k n ω) else 0 := fun n => by
    by_cases h : n < K k ω
    · rw [if_pos h, if_pos h, lintegral_dirac' _ hg]
    · rw [if_neg h, if_neg h, lintegral_zero_measure]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω))
    fun n hn => if_neg (by simpa [Finset.mem_range] using hn)]
  exact Finset.sum_congr rfl fun n hn => if_pos (by simpa [Finset.mem_range] using hn)
