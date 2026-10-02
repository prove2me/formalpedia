-- Prove2me | solution 1 for PricingRM.DetHeuristic.gallego_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:18:41.867754+00:00
-- url     : https://prove2.me/submissions/9b2443ff-0d48-46e4-83ab-194f94582b47

import Mathlib

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace E7a4e382Aux

lemma key {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (C : ℝ) :
    ∫ ω, max (X ω - C) 0 ∂P ≤
        (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) / 2 := by
  set Y : Ω → ℝ := fun ω => X ω - C with hYdef
  have hY : MemLp Y 2 P := hX.sub (memLp_const C)
  have hXi : Integrable X P := hX.integrable one_le_two
  have hYi : Integrable Y P := hY.integrable one_le_two
  have hVY : variance Y P = variance X P :=
    variance_sub_const hX.aestronglyMeasurable C
  have hEY : ∫ ω, Y ω ∂P = (∫ ω, X ω ∂P) - C := by
    simp only [hYdef]
    rw [integral_sub hXi (integrable_const C), integral_const]
    simp
  set A : Ω → ℝ := fun ω => |Y ω| with hAdef
  have hA : MemLp A 2 P := hY.abs
  have hAi : Integrable A P := hA.integrable one_le_two
  have hA2 : (A ^ 2) = (Y ^ 2) := by
    funext ω; simp [hAdef, sq_abs]
  have hvarA := variance_nonneg A P
  rw [variance_eq_sub hA, hA2] at hvarA
  have hvarY := variance_eq_sub hY
  rw [hVY] at hvarY
  -- (E A)^2 ≤ E[Y^2] = Var X + (C - E X)^2
  have hsq : (∫ ω, A ω ∂P) ^ 2 ≤ variance X P + (C - ∫ ω, X ω ∂P) ^ 2 := by
    have h1 : P[Y ^ 2] = variance X P + (∫ ω, Y ω ∂P) ^ 2 := by linarith
    rw [hEY] at h1
    have h2 : (∫ ω, A ω ∂P) ^ 2 ≤ P[Y ^ 2] := by linarith
    calc (∫ ω, A ω ∂P) ^ 2 ≤ P[Y ^ 2] := h2
      _ = variance X P + (C - ∫ ω, X ω ∂P) ^ 2 := by rw [h1]; ring
  have hEA0 : 0 ≤ ∫ ω, A ω ∂P := integral_nonneg (fun ω => abs_nonneg _)
  have hEA : ∫ ω, A ω ∂P ≤ Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  have hmax : (fun ω => max (X ω - C) 0) = fun ω => (Y ω + A ω) / 2 := by
    funext ω
    simp only [hAdef, hYdef]
    rcases le_total 0 (X ω - C) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  rw [hmax, integral_div, integral_add hYi hAi, hEY]
  linarith

end E7a4e382Aux

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (C : ℝ) :
    ∫ ω, max (X ω - C) 0 ∂P ≤
        (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) / 2 ∧
      (0 < ∫ ω, X ω ∂P → ∫ ω, X ω ∂P ≤ C →
        (∫ ω, max (X ω - C) 0 ∂P) / (∫ ω, X ω ∂P) ≤
            (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) /
              (2 * ∫ ω, X ω ∂P) ∧
          (Real.sqrt (variance X P + (C - ∫ ω, X ω ∂P) ^ 2) - (C - ∫ ω, X ω ∂P)) /
              (2 * ∫ ω, X ω ∂P) ≤
            (Real.sqrt (variance X P) / ∫ ω, X ω ∂P) / 2) := by
  have hk := E7a4e382Aux.key P X hX C
  refine ⟨hk, fun hpos hle => ⟨?_, ?_⟩⟩
  · have h := div_le_div_of_nonneg_right hk hpos.le
    rwa [div_div] at h
  · set m := ∫ ω, X ω ∂P
    set V := variance X P
    have hV : 0 ≤ V := variance_nonneg X P
    have ha : 0 ≤ C - m := by linarith
    have hs : Real.sqrt (V + (C - m) ^ 2) ≤ Real.sqrt V + (C - m) := by
      have h0 := Real.sqrt_nonneg V
      have h1 := Real.sq_sqrt hV
      exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
    rw [div_div, mul_comm m 2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
