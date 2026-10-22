-- Prove2me | solution 1 for ReedGGN.SystemEq.prop_2_1_reverse_argument
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:13:12.834614+00:00
-- url     : https://prove2.me/submissions/ee987cdd-12d6-47dc-a108-b77cde008dfb

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
    ∫ s in Set.Icc 0 t,
        (∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), if t - s < P.wt i then (1 : ℝ) else 0) ∂μ =
      ∑ i ∈ Finset.Icc 1 (P.Q₀ - P.N), (G μ (t - P.wt i) - G μ t) := by
  have hind : ∀ i, (fun s : ℝ => if t - s < P.wt i then (1 : ℝ) else 0) =
      (Set.Ioi (t - P.wt i)).indicator (fun _ => (1 : ℝ)) := by
    intro i; funext s
    by_cases h : t - s < P.wt i
    · have : s ∈ Set.Ioi (t - P.wt i) := by simp only [Set.mem_Ioi]; linarith
      simp [h, this]
    · have : s ∉ Set.Ioi (t - P.wt i) := by simp only [Set.mem_Ioi, not_lt]; linarith
      simp [h, this]
  have hint : ∀ i ∈ Finset.Icc 1 (P.Q₀ - P.N),
      Integrable (fun s : ℝ => if t - s < P.wt i then (1 : ℝ) else 0) (μ.restrict (Set.Icc 0 t)) := by
    intro i _
    rw [hind i]
    exact (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  rw [integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hab : t - P.wt i ≤ t := by linarith [P.wt_nonneg i]
  rw [rgg_key μ hμ _ _ hab, hind i, integral_indicator measurableSet_Ioi, setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply measurableSet_Ioi]
  congr 2
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc, Set.mem_Ici]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3⟩
