-- Prove2me | solution 1 for QueueingFundamentals.Bounds.idle_time_mean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:41:20.008988+00:00
-- url     : https://prove2.me/submissions/b22af294-05f4-4237-9cad-95ef0280ec15

import Mathlib
import Definitions.Def_QueueingFundamentals_Bounds_GG1

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable def p8b_clampK (K w : ℝ) : ℝ := max (min w K) (-K)

lemma p8b_clampK_lip (K a b : ℝ) : |p8b_clampK K a - p8b_clampK K b| ≤ |a - b| := by
  unfold p8b_clampK
  calc |max (min a K) (-K) - max (min b K) (-K)| ≤ |min a K - min b K| :=
        abs_max_sub_max_le_abs _ _ _
    _ ≤ max |a - b| |K - K| := abs_min_sub_min_le_max _ _ _ _
    _ = |a - b| := by simp

lemma p8b_clampK_cont (K : ℝ) : Continuous (p8b_clampK K) := by
  unfold p8b_clampK; fun_prop

lemma p8b_clampK_abs (K w : ℝ) (hK : 0 ≤ K) : |p8b_clampK K w| ≤ K := by
  unfold p8b_clampK; rw [abs_le]; constructor
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (by linarith)

lemma p8b_clampK_eq (K w : ℝ) (h : |w| ≤ K) : p8b_clampK K w = w := by
  unfold p8b_clampK; rw [abs_le] at h
  rw [min_eq_left h.2, max_eq_left h.1]

open QueueingFundamentals.Bounds MeasureTheory ProbabilityTheory Filter Topology in
theorem solution
    {A B ν : Measure ℝ} {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu)
    (hin : IsGG1Input A B lam mu) (hrho : lam / mu < 1) (hν : IsStationaryWaitLaw A B ν) :
    (∀ w s t : ℝ, lindley w s t - idleX w s t = w + (s - t)) ∧
    ∫ p, idleX p.1 p.2.1 p.2.2 ∂(stepLaw ν B A) = -∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) ∧
    -∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) = 1 / lam - 1 / mu := by
  have := hν.isProbability
  have := hin.isProbability_interarrival
  have := hin.isProbability_service
  have hμ : stepLaw ν B A = ν.prod (B.prod A) := rfl
  have : IsProbabilityMeasure (stepLaw ν B A) := by rw [hμ]; infer_instance
  have hpath : ∀ w s t : ℝ, lindley w s t - idleX w s t = w + (s - t) := by
    intro w s t; unfold lindley idleX
    rcases le_total 0 (w + (s - t)) with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]; ring
  have hBi : Integrable (fun x : ℝ => x) B := hin.service_memLp.integrable (by norm_num)
  have hAi : Integrable (fun x : ℝ => x) A := hin.interarrival_memLp.integrable (by norm_num)
  have hSA : Integrable (fun q : ℝ × ℝ => q.1 - q.2) (B.prod A) :=
    (hBi.comp_fst A).sub (hAi.comp_snd B)
  have hU : Integrable (fun p : ℝ × ℝ × ℝ => p.2.1 - p.2.2) (stepLaw ν B A) := by
    rw [hμ]; exact hSA.comp_snd ν
  have hEU : ∫ p, (p.2.1 - p.2.2) ∂(stepLaw ν B A) = 1 / mu - 1 / lam := by
    rw [hμ]
    have h1 := integral_fun_snd (μ := ν) (ν := B.prod A) (fun q : ℝ × ℝ => q.1 - q.2)
    try simp only at h1
    rw [h1, integral_sub (hBi.comp_fst A) (hAi.comp_snd B)]
    have h2 := integral_fun_fst (μ := B) (ν := A) (fun x : ℝ => x)
    have h3 := integral_fun_snd (μ := B) (ν := A) (fun x : ℝ => x)
    try simp only at h2 h3
    rw [h2, h3, hin.service_mean, hin.interarrival_mean]
    simp
  have hlm : Measurable (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) := by
    unfold lindley; fun_prop
  have hν0 : ν (Set.Iio 0) = 0 := by
    rw [← hν.invariant, Measure.map_apply hlm measurableSet_Iio]
    have : (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2) ⁻¹' Set.Iio 0 = ∅ := by
      ext p; simp [lindley]
    rw [this, measure_empty]
  have hW : ∀ᵐ p ∂(stepLaw ν B A), 0 ≤ p.1 := by
    rw [ae_iff, hμ]
    have : {p : ℝ × ℝ × ℝ | ¬ 0 ≤ p.1} = Set.Iio 0 ×ˢ Set.univ := by
      ext p; simp
    rw [this, Measure.prod_prod, hν0, zero_mul]
  have hXc : Continuous (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) := by
    unfold idleX; fun_prop
  have hXi : Integrable (fun p : ℝ × ℝ × ℝ => idleX p.1 p.2.1 p.2.2) (stepLaw ν B A) := by
    refine Integrable.mono' hU.abs hXc.aestronglyMeasurable ?_
    filter_upwards [hW] with p hp
    rw [Real.norm_eq_abs]
    unfold idleX
    rcases le_total 0 (p.1 + (p.2.1 - p.2.2)) with h | h
    · rw [min_eq_left h]; simp
    · rw [min_eq_right h, abs_neg, abs_of_nonpos h]
      have := neg_abs_le (p.2.1 - p.2.2)
      linarith
  have hfeq : (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2 - p.1) =
      fun p => idleX p.1 p.2.1 p.2.2 + (p.2.1 - p.2.2) := by
    funext p; have := hpath p.1 p.2.1 p.2.2; linarith
  have hD : Integrable (fun p : ℝ × ℝ × ℝ => lindley p.1 p.2.1 p.2.2 - p.1) (stepLaw ν B A) := by
    rw [hfeq]; exact hXi.add hU
  have hzero : ∫ p, (lindley p.1 p.2.1 p.2.2 - p.1) ∂(stepLaw ν B A) = 0 := by
    have hlim := tendsto_integral_of_dominated_convergence
      (μ := stepLaw ν B A)
      (F := fun (n : ℕ) (p : ℝ × ℝ × ℝ) => p8b_clampK n (lindley p.1 p.2.1 p.2.2) - p8b_clampK n p.1)
      (f := fun p => lindley p.1 p.2.1 p.2.2 - p.1)
      (fun p => |lindley p.1 p.2.1 p.2.2 - p.1|)
      (fun n => (((p8b_clampK_cont n).measurable.comp hlm).sub
        ((p8b_clampK_cont n).measurable.comp measurable_fst)).aestronglyMeasurable)
      hD.abs
      (fun n => ae_of_all _ fun p => by
        rw [Real.norm_eq_abs]; exact p8b_clampK_lip _ _ _)
      (ae_of_all _ fun p => by
        apply tendsto_atTop_of_eventually_const
          (i₀ := ⌈max |lindley p.1 p.2.1 p.2.2| |p.1|⌉₊)
        intro n hn
        have hc : max |lindley p.1 p.2.1 p.2.2| |p.1| ≤ (n : ℝ) :=
          (Nat.le_ceil _).trans (by exact_mod_cast hn)
        try simp only
        rw [p8b_clampK_eq _ _ ((le_max_left _ _).trans hc), p8b_clampK_eq _ _ ((le_max_right _ _).trans hc)])
    have hconst : ∀ n : ℕ, ∫ p, (p8b_clampK n (lindley p.1 p.2.1 p.2.2) - p8b_clampK n p.1)
        ∂(stepLaw ν B A) = 0 := by
      intro n
      have hc := p8b_clampK_cont n
      have hbi : ∀ f : ℝ × ℝ × ℝ → ℝ, Measurable f →
          Integrable (fun p => p8b_clampK n (f p)) (stepLaw ν B A) := fun f hf =>
        (integrable_const (n : ℝ)).mono' (hc.measurable.comp hf).aestronglyMeasurable
          (ae_of_all _ fun p => by
            rw [Real.norm_eq_abs]; exact p8b_clampK_abs _ _ (Nat.cast_nonneg n))
      rw [integral_sub (hbi _ hlm) (hbi _ measurable_fst)]
      have e1 : ∫ p, p8b_clampK n (lindley p.1 p.2.1 p.2.2) ∂(stepLaw ν B A)
          = ∫ w, p8b_clampK n w ∂ν := by
        conv_rhs => rw [← hν.invariant]
        rw [integral_map hlm.aemeasurable hc.aestronglyMeasurable]
      have e2 : ∫ p, p8b_clampK n p.1 ∂(stepLaw ν B A) = ∫ w, p8b_clampK n w ∂ν := by
        rw [hμ, integral_fun_fst]; simp
      rw [e1, e2, sub_self]
    simp only [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  refine ⟨hpath, ?_, ?_⟩
  · have h := hzero
    rw [hfeq, integral_add hXi hU] at h
    linarith
  · rw [hEU]; ring
