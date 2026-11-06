-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:41:41.93853+00:00
-- url     : https://prove2.me/submissions/d5bc33d2-bca8-49c8-b18a-f1a303bf939d

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) : SigmaFinite ν := by
  have hfinite {ε : ℝ} (hε : 0 < ε) :
      ν {x | ε ≤ |x|} < ⊤ := by
    set c := ENNReal.ofReal (min 1 (ε ^ 2))
    set f := fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2))
    have hε2 : 0 < min 1 (ε ^ 2) := lt_min one_pos (sq_pos_of_pos hε)
    have hc_pos : 0 < c := ENNReal.ofReal_pos.mpr hε2
    have hf_meas : Measurable f := by
      apply ENNReal.measurable_ofReal.comp
      exact measurable_const.min (measurable_id'.pow_const 2)
    have hSub : {x : ℝ | ε ≤ |x|} ⊆ {x : ℝ | c ≤ f x} := by
      intro x hx
      simp only [mem_setOf_eq] at hx ⊢
      apply ENNReal.ofReal_le_ofReal
      exact min_le_min le_rfl ((sq_abs x).symm ▸ pow_le_pow_left₀ hε.le hx 2)
    have hMarkov := mul_meas_ge_le_lintegral hf_meas c (μ := ν)
    have hle : c * ν {x | ε ≤ |x|} ≤ ∫⁻ x, f x ∂ν :=
      le_trans (mul_le_mul_right (measure_mono hSub) c) hMarkov
    exact lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top hν.2.ne hle) hc_pos.ne'
  constructor
  exact ⟨{
    set := fun n => {x : ℝ | (1 : ℝ) / (↑(n + 1) : ℝ) ≤ |x|} ∪ {0}
    set_mem := fun _ => trivial
    finite := fun n => by
      calc ν ({x : ℝ | 1 / (↑(n + 1) : ℝ) ≤ |x|} ∪ {0})
          ≤ ν {x : ℝ | 1 / (↑(n + 1) : ℝ) ≤ |x|} + ν {0} := measure_union_le _ _
        _ = ν {x : ℝ | 1 / (↑(n + 1) : ℝ) ≤ |x|} + 0 := by rw [hν.1]
        _ = ν {x : ℝ | 1 / (↑(n + 1) : ℝ) ≤ |x|} := add_zero _
        _ < ⊤ := hfinite (by positivity)
    spanning := by
      ext x
      simp only [mem_iUnion, mem_union, mem_setOf_eq, mem_singleton_iff, mem_univ, iff_true]
      by_cases hx : x = 0
      · exact ⟨0, Or.inr hx⟩
      · have habs : 0 < |x| := abs_pos.mpr hx
        obtain ⟨n, hn⟩ := exists_nat_gt (1 / |x|)
        refine ⟨n, Or.inl ?_⟩
        rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos n))]
        have h1 : 1 / |x| < ↑n := hn
        rw [div_lt_iff₀ habs] at h1
        have h2 : (↑n : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.le_succ n
        nlinarith
  }⟩
