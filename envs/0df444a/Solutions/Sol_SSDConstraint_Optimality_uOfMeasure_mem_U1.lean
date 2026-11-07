-- Prove2me | solution 1 for SSDConstraint.Optimality.uOfMeasure_mem_U1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:06:04.108244+00:00
-- url     : https://prove2.me/submissions/9e6e279e-63af-4116-9152-247eff248e65

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Multiplier

open MeasureTheory SSDConstraint.Optimality

theorem nl2_neg_u_eq (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Icc a b)ᶜ = 0) (t : ℝ) :
    -uOfMeasure μ b t = ∫ η in Set.Icc a b, max (η - t) 0 ∂μ := by
  have hres : μ.restrict (Set.Icc a b) = μ :=
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono
      (fun x hx => by simpa using hx))
  unfold uOfMeasure
  split_ifs with htb
  · rw [neg_neg, intervalIntegral.integral_of_le htb.le]
    -- μ.real (Icc τ b) as an integral
    have h1 : ∀ τ, μ.real (Set.Icc τ b) =
        ∫ η, (Set.Icc τ b).indicator (fun _ => (1 : ℝ)) η ∂μ := fun τ =>
      (integral_indicator_one measurableSet_Icc).symm
    simp_rw [h1]
    set F : ℝ → ℝ → ℝ := fun τ η => (Set.Icc τ b).indicator (fun _ => (1 : ℝ)) η with hF
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ b} :=
      (measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    have hFu : Function.uncurry F = {p : ℝ × ℝ | p.1 ≤ p.2 ∧ p.2 ≤ b}.indicator (fun _ => 1) := by
      funext p
      simp only [Function.uncurry, F, Set.indicator, Set.mem_Icc, Set.mem_ofPred_eq]
    have hint : Integrable (Function.uncurry F) ((volume.restrict (Set.Ioc t b)).prod μ) := by
      rw [hFu]; exact (integrable_const (1 : ℝ)).indicator hS
    rw [integral_integral_swap hint]
    rw [hres]
    have hae : ∀ᵐ η ∂μ, η ∈ Set.Icc a b :=
      measure_eq_zero_iff_ae_notMem.1 hsupp |>.mono (fun x hx => by simpa using hx)
    refine integral_congr_ae (hae.mono (fun η hη => ?_))
    have e1 : ∫ τ in Set.Ioc t b, F τ η = ∫ τ in Set.Ioc t b, (Set.Iic η).indicator (fun _ => (1:ℝ)) τ := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
      simp only [F, Set.indicator, Set.mem_Icc, Set.mem_Iic]
      by_cases h : τ ≤ η
      · simp [h, hη.2]
      · simp [h]
    show ∫ τ in Set.Ioc t b, F τ η = max (η - t) 0
    rw [e1, integral_indicator_const (1:ℝ) measurableSet_Iic, smul_eq_mul, mul_one,
      measureReal_restrict_apply measurableSet_Iic]
    have e2 : Set.Iic η ∩ Set.Ioc t b = Set.Ioc t η := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans hη.2⟩
    rw [e2, Real.volume_real_Ioc]
  · push Not at htb
    rw [neg_zero]
    symm
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0:ℝ)) (fun η hη => by
      simp only; exact max_eq_right (by linarith [hη.2]))]
    simp


theorem nl2_kink_integrableOn (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    IntegrableOn (fun η : ℝ => max (η - t) 0) (Set.Icc a b) μ :=
  (by fun_prop : Continuous fun η : ℝ => max (η - t) 0).continuousOn.integrableOn_compact
    isCompact_Icc

theorem solution (a b : ℝ) :
    ∀ μ : Measure ℝ, IsFiniteMeasure μ → μ (Set.Icc a b)ᶜ = 0 → uOfMeasure μ b ∈ U1 a b := by
  intro μ hμ hsupp
  have hrep : ∀ t, uOfMeasure μ b t = -∫ η in Set.Icc a b, max (η - t) 0 ∂μ := fun t => by
    rw [← nl2_neg_u_eq a b μ hsupp t, neg_neg]
  have hI := nl2_kink_integrableOn a b μ
  refine ⟨⟨convex_univ, fun x _ y _ α β hα hβ hαβ => ?_⟩, fun x y hxy => ?_, fun t ht => ?_, ?_⟩
  · simp only [hrep, smul_eq_mul]
    have hle : (∫ η in Set.Icc a b, max (η - (α * x + β * y)) 0 ∂μ) ≤
        ∫ η in Set.Icc a b, (α * max (η - x) 0 + β * max (η - y) 0) ∂μ := by
      refine integral_mono (hI _) (((hI x).const_mul α).add ((hI y).const_mul β)) (fun η => ?_)
      simp only
      refine max_le ?_ (by positivity)
      have e : η - (α * x + β * y) = α * (η - x) + β * (η - y) := by
        have : η = (α + β) * η := by rw [hαβ, one_mul]
        linear_combination this
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left (le_max_left (η - x) 0) hα
      have h2 := mul_le_mul_of_nonneg_left (le_max_left (η - y) 0) hβ
      linarith
    rw [integral_add ((hI x).const_mul α) ((hI y).const_mul β), integral_const_mul,
      integral_const_mul] at hle
    linarith
  · simp only [hrep, neg_le_neg_iff]
    refine integral_mono (hI y) (hI x) (fun η => ?_)
    exact max_le_max (by linarith) le_rfl
  · unfold uOfMeasure
    rw [if_neg (not_lt.2 ht)]
  · refine ⟨μ.real (Set.Icc a b), measureReal_nonneg, fun t hta => ?_⟩
    have hlin : ∀ s ≤ a, (∫ η in Set.Icc a b, max (η - s) 0 ∂μ) =
        (∫ η in Set.Icc a b, (η - a) ∂μ) + μ.real (Set.Icc a b) * (a - s) := by
      intro s hs
      have hIa : IntegrableOn (fun η : ℝ => η - a) (Set.Icc a b) μ :=
        (by fun_prop : Continuous fun η : ℝ => η - a).continuousOn.integrableOn_compact
          isCompact_Icc
      rw [setIntegral_congr_fun measurableSet_Icc (g := fun η => (η - a) + (a - s))
        (fun η hη => by simp only; rw [max_eq_left (by linarith [hη.1])]; ring),
        integral_add hIa (integrable_const _), setIntegral_const, smul_eq_mul]
    rw [hrep, hrep, hlin t hta, hlin a le_rfl]
    ring
