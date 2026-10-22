-- Prove2me | solution 1 for RobustPower.CostGap.eq_3_2_expected_min_uniform
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:18:12.68699+00:00
-- url     : https://prove2.me/submissions/e63d9d71-b089-47c8-b36f-bd27af4a98d4

import Mathlib

open MeasureTheory


namespace RobustPower.CostGap

instance g25_prob_Icc : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp⟩

lemma g25_lt_iInf_iff {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (t : ℝ) :
    t < (⨅ j, x j) ↔ ∀ j, t < x j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · intro h j
    exact lt_of_lt_of_le h (ciInf_le (Finite.bddBelow_range _) j)
  · intro h
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi]; exact h i

lemma g25_expected_min_pi {n : ℕ} (hn : 0 < n) :
    ∫ x, (⨅ j, x j) ∂(Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)))
      = 1 / ((n : ℝ) + 1) := by
  set ν := Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) with hν
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hmeas : Measurable (fun x : Fin n → ℝ => ⨅ j, x j) :=
    Measurable.iInf (fun j => measurable_pi_apply j)
  have hae : ∀ᵐ x ∂ν, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro j
    have hmp := measurePreserving_eval (μ := fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) j
    have h1 : ∀ᵐ y ∂(ν.map (Function.eval j)), y ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hmp.map_eq]; exact ae_restrict_mem measurableSet_Icc
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable h1
  have hint : Integrable (fun x : Fin n → ℝ => ⨅ j, x j) ν := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
    rw [← hi, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hx i).1], (hx i).2⟩
  have hnn : 0 ≤ᵐ[ν] (fun x : Fin n → ℝ => ⨅ j, x j) := by
    filter_upwards [hae] with x hx
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := x)
    show 0 ≤ ⨅ j, x j
    rw [← hi]; exact (hx i).1
  rw [hint.integral_eq_integral_meas_lt hnn]
  have hset : ∀ t ∈ Set.Ioi (0 : ℝ), ν.real {a | t < ⨅ j, a j} = (max (1 - t) 0) ^ n := by
    intro t ht
    have : {a : Fin n → ℝ | t < ⨅ j, a j} = Set.univ.pi (fun _ => Set.Ioi t) := by
      ext a; simp [g25_lt_iInf_iff hn]
    rw [this, measureReal_def, hν, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    congr 1
    rw [Measure.restrict_apply measurableSet_Ioi]
    have : Set.Ioi t ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc t 1 := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [Set.mem_Ioi.mp ht], h3⟩
    rw [this, Real.volume_Ioc, ENNReal.toReal_ofReal']
  rw [setIntegral_congr_fun measurableSet_Ioi hset]
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ioc 0 1) Set.Ioc_subset_Ioi_self]
  swap
  · intro x hx
    simp only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le] at hx
    have : max (1 - x) 0 = 0 := max_eq_right (by linarith [hx.2 hx.1])
    rw [this, zero_pow hn.ne']
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hc : ∫ x in (0:ℝ)..1, (max (1 - x) 0) ^ n = ∫ x in (0:ℝ)..1, (1 - x) ^ n := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only
    rw [max_eq_left (by linarith [hx.2])]
  rw [hc, intervalIntegral.integral_comp_sub_left (fun x => x ^ n) (1 : ℝ)]
  simp [integral_pow]

theorem eq_3_2_core {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ ω, (⨅ j, d ω j) ∂μ = 1 / ((n : ℝ) + 1) := by
  have hmeas : Measurable (fun x : Fin n → ℝ => ⨅ j, x j) :=
    Measurable.iInf (fun j => measurable_pi_apply j)
  have := integral_map (μ := μ) hd.aemeasurable (hmeas.aestronglyMeasurable)
  rw [hlaw] at this
  rw [← g25_expected_min_pi hn, this]

end RobustPower.CostGap

open RobustPower.CostGap


theorem solution {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    ∫ ω, (⨅ j, d ω j) ∂μ = 1 / ((n : ℝ) + 1) := by
  exact eq_3_2_core hn μ d hd hlaw
