-- Prove2me | solution 1 for SmoothNestedSim.lemma_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:27:08.262669+00:00
-- url     : https://prove2.me/submissions/ac4d119c-d004-4225-8775-400f3f2fd3d3

import Mathlib
import Definitions.Def_SmoothNestedSim_IsBigOP

open MeasureTheory ProbabilityTheory

open SmoothNestedSim in
theorem solution {S : ℕ → Type*} [∀ k, MeasurableSpace (S k)] (P : ∀ k, Measure (S k))
    [∀ k, IsProbabilityMeasure (P k)] (Z : ∀ k, S k → ℝ) (hZ : ∀ k, MemLp (Z k) 2 (P k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂(P k) = 0) :
    IsBigOP P (fun k ω => |Z k ω|) (fun k => Real.sqrt (variance (Z k) (P k))) := by
  intro ε hε
  have hC : 0 < Real.sqrt (2 / ε) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨Real.sqrt (2 / ε), hC, Filter.Eventually.of_forall (fun k => ?_)⟩
  have hσ0 : 0 ≤ Real.sqrt (variance (Z k) (P k)) := Real.sqrt_nonneg _
  have hvar0 := variance_nonneg (Z k) (P k)
  rcases hσ0.lt_or_eq with hσ | hσ
  · have hc : 0 < Real.sqrt (2 / ε) * Real.sqrt (variance (Z k) (P k)) := mul_pos hC hσ
    have hv : 0 < variance (Z k) (P k) := Real.sqrt_pos.mp hσ
    calc P k {ω | Real.sqrt (2 / ε) * Real.sqrt (variance (Z k) (P k)) < |Z k ω|}
        ≤ P k {ω | Real.sqrt (2 / ε) * Real.sqrt (variance (Z k) (P k)) ≤
            |Z k ω - ∫ ω, Z k ω ∂(P k)|} := by
          apply measure_mono
          intro ω hω
          simp only [Set.mem_setOf_eq] at hω ⊢
          rw [hmean k, sub_zero]
          exact hω.le
      _ ≤ ENNReal.ofReal (variance (Z k) (P k) /
            (Real.sqrt (2 / ε) * Real.sqrt (variance (Z k) (P k))) ^ 2) :=
          meas_ge_le_variance_div_sq (hZ k) hc
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε]
          rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hvar0]
          have e : variance (Z k) (P k) / (2 / ε * variance (Z k) (P k)) = ε / 2 := by
            field_simp
          rw [e]
          linarith
  · have hvar : variance (Z k) (P k) = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp hσ.symm) hvar0
    have hae := ae_eq_integral_of_variance_eq_zero (hZ k) hvar
    have h2 : ∀ᵐ ω ∂(P k), ¬ (Real.sqrt (2 / ε) * Real.sqrt (variance (Z k) (P k)) < |Z k ω|) := by
      filter_upwards [hae] with ω hω
      rw [hω, hmean k, ← hσ]
      simp
    have h3 := ae_iff.mp h2
    simp only [not_not] at h3
    show P k {ω | Real.sqrt (2 / ε) * Real.sqrt (variance (Z k) (P k)) < |Z k ω|} < ENNReal.ofReal ε
    rw [h3]
    exact ENNReal.ofReal_pos.mpr hε
