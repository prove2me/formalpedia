-- Prove2me | solution 1 for OnlineNRM.TSFixed.full_demand_period_revenue_integrable_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T18:18:38.162085+00:00
-- url     : https://prove2.me/submissions/29b50169-8ab9-4a37-9ea2-e7a7a2c764bb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

open MeasureTheory ProbabilityTheory OnlineNRM.TSFixed
open scoped BigOperators OnlineNRM.TSFixed

theorem solution
    {N K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (p : Fin N → Fin K → ℝ) (dbar : Fin N → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → Ω → Option (Fin K)) (D : ℕ → Ω → Fin N → ℝ)
    (t : ℕ) (hp : ∀ i k, 0 ≤ p i k)
    (hA : Measurable (A t)) (hD : Measurable (D t))
    (hbound : ∀ᵐ ω ∂P, A t ω = none ∨ ∀ i, D t ω i ∈ Set.Icc 0 (dbar i)) :
    Integrable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) P := by
  classical
  let C : ℝ := ∑ i : Fin N, |dbar i| * ∑ k : Fin K, |p i k|
  have hposted : Measurable (fun a : Option (Fin K) => postedPrice p a) :=
    measurable_of_finite _
  have hmeas : Measurable (fun ω => ∑ i : Fin N, D t ω i * postedPrice p (A t ω) i) := by
    apply Finset.measurable_sum
    intro i hi
    have hDi : Measurable (fun ω => D t ω i) :=
      (continuous_apply i).measurable.comp hD
    have hPi : Measurable (fun ω => postedPrice p (A t ω) i) :=
      (continuous_apply i).measurable.comp (hposted.comp hA)
    exact hDi.mul hPi
  have hprice : ∀ a i, |postedPrice p a i| ≤ ∑ k : Fin K, |p i k| := by
    intro a i
    cases a with
    | none =>
      simp [postedPrice]
      positivity
    | some k =>
      simpa [postedPrice] using
        (Finset.single_le_sum (f := fun j : Fin K => |p i j|)
          (fun j hj => abs_nonneg (p i j)) (Finset.mem_univ k))
  have hdom : ∀ᵐ ω ∂P,
      ‖∑ i : Fin N, D t ω i * postedPrice p (A t ω) i‖ ≤ C := by
    filter_upwards [hbound] with ω hω
    rcases hω with hnone | hcoords
    · simp [hnone, postedPrice]
      positivity
    · rw [Real.norm_eq_abs]
      calc
        |∑ i : Fin N, D t ω i * postedPrice p (A t ω) i|
            ≤ ∑ i : Fin N, |D t ω i * postedPrice p (A t ω) i| :=
              Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin N, |dbar i| * ∑ k : Fin K, |p i k| := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := hcoords i
          have hd0 : 0 ≤ D t ω i := hi'.1
          have hdi : D t ω i ≤ dbar i := hi'.2
          have hdb0 : 0 ≤ dbar i := le_trans hd0 hdi
          have habs : |D t ω i| ≤ |dbar i| := by
            rw [abs_of_nonneg hd0, abs_of_nonneg hdb0]
            exact hdi
          calc
            |D t ω i * postedPrice p (A t ω) i|
                = |D t ω i| * |postedPrice p (A t ω) i| := abs_mul _ _
            _ ≤ |D t ω i| * ∑ k : Fin K, |p i k| :=
              mul_le_mul_of_nonneg_left (hprice (A t ω) i) (abs_nonneg _)
            _ ≤ |dbar i| * ∑ k : Fin K, |p i k| :=
              mul_le_mul_of_nonneg_right habs
                (Finset.sum_nonneg fun k hk => abs_nonneg (p i k))
        _ = C := by rfl
  exact (integrable_const C).mono' hmeas.aestronglyMeasurable hdom