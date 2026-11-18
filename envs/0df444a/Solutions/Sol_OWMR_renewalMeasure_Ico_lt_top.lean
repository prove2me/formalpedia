-- Prove2me | solution 1 for OWMR.renewalMeasure_Ico_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Ming Hu
-- created : 2026-11-16T02:43:04.920299+00:00
-- url     : https://prove2.me/submissions/826e2014-98b8-40e7-8b9e-6ebf4d1cb2dd

import Definitions.Def_owmr_renewal
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Finiteness of `M(w) = U[0,w)` (footnote to (9)). With `c = 𝔼 e^{-D} < 1` (positive mean demand),
the exponential (Chernoff) bound `ℙ(D^{(k)} < w) ≤ e^{w} c^{k}` makes the series `∑_k ℙ(D^{(k)} < w)`
dominated by a convergent geometric series.
-/

open MeasureTheory
open scoped ENNReal NNReal
open OWMR

private lemma measurable_psum (k : ℕ) : Measurable (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) :=
  Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).coe_nnreal_real

theorem solution (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (w : ℝ) : renewalMeasure ρ (Set.Ico 0 w) < ∞ := by
  have hem : Measurable fun x : ℝ≥0 => Real.exp (-(x : ℝ)) :=
    Real.measurable_exp.comp measurable_coe_nnreal_real.neg
  have hle1 : ∀ x : ℝ≥0, Real.exp (-(x : ℝ)) ≤ 1 := fun x =>
    Real.exp_le_one_iff.2 (neg_nonpos.2 x.2)
  have hint : Integrable (fun x : ℝ≥0 => Real.exp (-(x : ℝ))) ρ :=
    (integrable_const (1 : ℝ)).mono' hem.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle1 x)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ x, Real.exp (-(x : ℝ)) ∂ρ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ integral_nonneg fun x => (Real.exp_pos _).le
  -- `c < 1` because demand is not almost surely zero
  have hc1 : c < 1 := by
    have hpos : 0 < ∫ x, (1 - Real.exp (-(x : ℝ))) ∂ρ := by
      have hint2 : Integrable (fun x : ℝ≥0 => 1 - Real.exp (-(x : ℝ))) ρ :=
        (integrable_const 1).sub hint
      rw [integral_pos_iff_support_of_nonneg (f := fun x : ℝ≥0 => 1 - Real.exp (-(x : ℝ)))
        (fun x => by simp only [Pi.zero_apply, sub_nonneg]; exact hle1 x) hint2]
      have hsupp : Function.support (fun x : ℝ≥0 => 1 - Real.exp (-(x : ℝ)))
          = Function.support (fun x : ℝ≥0 => (x : ℝ≥0∞)) := by
        ext x
        simp only [Function.mem_support, ne_eq, sub_eq_zero, ENNReal.coe_eq_zero]
        constructor
        · intro h hx
          exact h (by simp [hx])
        · intro h h1
          have : -(x : ℝ) = 0 := Real.exp_eq_one_iff _ |>.1 h1.symm
          exact h (by simpa using this)
      rw [hsupp, ← lintegral_pos_iff_support measurable_coe_nnreal_ennreal]
      exact hρ
    rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, one_smul,
      ← hc] at hpos
    linarith
  -- the exponential bound on each term
  have hterm : ∀ k : ℕ, (Measure.pi fun _ : Fin k => ρ)
      ((fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w)
        ≤ ENNReal.ofReal (Real.exp w) * ENNReal.ofReal c ^ k := by
    intro k
    have hS : MeasurableSet ((fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w) :=
      measurable_psum k measurableSet_Ico
    have hprod_m : Measurable fun z : Fin k → ℝ≥0 => ∏ j, Real.exp (-(z j : ℝ)) :=
      Finset.measurable_prod _ fun j _ => hem.comp (measurable_pi_apply j)
    have hprod_i : Integrable (fun z : Fin k → ℝ≥0 => ∏ j, Real.exp (-(z j : ℝ)))
        (Measure.pi fun _ : Fin k => ρ) :=
      (integrable_const (1 : ℝ)).mono' hprod_m.aestronglyMeasurable (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
        exact Finset.prod_le_one (fun j _ => (Real.exp_pos _).le) fun j _ => hle1 (z j))
    have hpow := integral_fintype_prod_eq_pow (ι := Fin k) (fun x : ℝ≥0 => Real.exp (-(x : ℝ)))
      (μ := ρ)
    simp only [Fintype.card_fin] at hpow
    have hreal : (Measure.pi fun _ : Fin k => ρ).real
        ((fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w) ≤ Real.exp w * c ^ k := by
      rw [← integral_indicator_one hS]
      calc ∫ z, ((fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w).indicator 1 z
            ∂(Measure.pi fun _ : Fin k => ρ)
          ≤ ∫ z, Real.exp w * ∏ j, Real.exp (-(z j : ℝ)) ∂(Measure.pi fun _ : Fin k => ρ) := by
            refine integral_mono ((integrable_const (1 : ℝ)).indicator hS)
              (hprod_i.const_mul _) fun z => ?_
            by_cases hz : z ∈ (fun z : Fin k → ℝ≥0 => ∑ j, (z j : ℝ)) ⁻¹' Set.Ico 0 w
            · rw [Set.indicator_of_mem hz, Pi.one_apply, ← Real.exp_sum, ← Real.exp_add]
              refine Real.one_le_exp ?_
              have := hz.2
              simp only [Finset.sum_neg_distrib] at this ⊢
              linarith
            · rw [Set.indicator_of_notMem hz]
              positivity
        _ = Real.exp w * c ^ k := by rw [integral_const_mul, hpow, ← hc]
    rw [← ofReal_measureReal (measure_ne_top _ _), ← ENNReal.ofReal_pow hc0,
      ← ENNReal.ofReal_mul (Real.exp_pos w).le]
    exact ENNReal.ofReal_le_ofReal hreal
  have hsum : renewalMeasure ρ (Set.Ico 0 w)
      ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp w) * ENNReal.ofReal c ^ k := by
    unfold renewalMeasure
    rw [Measure.sum_apply _ measurableSet_Ico]
    refine ENNReal.tsum_le_tsum fun k => ?_
    rw [Measure.map_apply (measurable_psum k) measurableSet_Ico]
    exact hterm k
  refine lt_of_le_of_lt hsum ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  rw [ENNReal.inv_lt_top]
  exact tsub_pos_of_lt (ENNReal.ofReal_lt_one.2 hc1)
