-- Prove2me | solution 1 for ReedGGN.SystemEq.prop_2_1_arrival_delay
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:13:11.628542+00:00
-- url     : https://prove2.me/submissions/2c062e26-2fb2-4c37-83a8-49e3d9096bd1

import Mathlib
import Definitions.Def_ReedGGN_SystemEq_QueueLength

set_option autoImplicit false
open MeasureTheory ReedGGN.SystemEq

lemma rgg_key (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0) (a b : ℝ)
    (hab : a ≤ b) : G μ a - G μ b = (μ (Set.Ioc a b ∩ Set.Ici 0)).toReal := by
  have h1 : μ (Set.Ioi a) = μ (Set.Ioc a b) + μ (Set.Ioi b) := by
    rw [← measure_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi, Set.Ioc_union_Ioi_eq_Ioi hab]
  have h2 : μ (Set.Ioc a b ∩ Set.Ici 0) = μ (Set.Ioc a b) := by
    have : Set.Ioc a b ∩ Set.Ici 0 = Set.Ioc a b \ Set.Iio 0 := by
      rw [Set.diff_eq, Set.compl_Iio]
    rw [this, measure_diff_null hμ]
  rw [h2]
  unfold G
  rw [h1, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  ring

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (P : SamplePath) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i ∈ Finset.Icc 1 (P.A t), (G μ (t - P.τ i - P.w i) - G μ (t - P.τ i)) =
      ∑ i ∈ Finset.Icc 1 (P.A t),
        ∫ s in Set.Ici 0, (Set.Ioc (t - (P.τ i + P.w i)) (t - P.τ i)).indicator
          (fun _ => (1 : ℝ)) s ∂μ := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hab : t - P.τ i - P.w i ≤ t - P.τ i := by linarith [P.w_nonneg i]
  rw [rgg_key μ hμ _ _ hab, ← sub_sub,
    integral_indicator measurableSet_Ioc, setIntegral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply measurableSet_Ioc]

