-- Prove2me | solution 1 for SRPTManyServer.Collapse.problem_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T19:41:50.091496+00:00
-- url     : https://prove2.me/submissions/1b5bbe24-486e-492e-8d9b-c905c9fb300c

import Mathlib

open MeasureTheory

namespace Aux_SRPTp7

lemma int_mul (h φ : ℝ → ℝ) (hh : IntegrableOn h (Set.Ici 0)) (hφm : Measurable φ)
    (hφ : ∀ x, 0 ≤ x → φ x ∈ Set.Icc (0:ℝ) 1) :
    IntegrableOn (fun x => h x * φ x) (Set.Ici 0) := by
  refine Integrable.mono' hh.norm (hh.aestronglyMeasurable.mul hφm.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with x hx
  rw [norm_mul]
  have := hφ x hx
  calc ‖h x‖ * ‖φ x‖ ≤ ‖h x‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
    _ = ‖h x‖ := mul_one _

lemma ind_int (τ : ℝ) (h : ℝ → ℝ) :
    ∫ x in Set.Ici 0, h x * (Set.Iic τ).indicator (fun _ => (1:ℝ)) x =
      ∫ x in Set.Icc 0 τ, h x := by
  have : (fun x => h x * (Set.Iic τ).indicator (fun _ => (1:ℝ)) x) = (Set.Iic τ).indicator h := by
    funext x; by_cases hx : x ∈ Set.Iic τ <;> simp [hx]
  rw [this, setIntegral_indicator measurableSet_Iic, Set.Ici_inter_Iic]

end Aux_SRPTp7

open Aux_SRPTp7 in
theorem solution (g : ℝ → ℝ) (hg_meas : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hg_int : IntegrableOn g (Set.Ici 0))
    (hxg_int : IntegrableOn (fun x => x * g x) (Set.Ici 0)) (tau : ℝ) :
    IsLeast
      {v : ℝ | ∃ γ : ℝ → ℝ, Measurable γ ∧ (∀ x, 0 ≤ x → γ x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ x in Set.Icc 0 tau, g x) ≤ (∫ x in Set.Ici 0, g x * γ x) ∧
        v = ∫ x in Set.Ici 0, x * g x * γ x}
      (∫ x in Set.Icc 0 tau, x * g x) ∧
    (∫ x in Set.Icc 0 tau, g x) ≤
        (∫ x in Set.Ici 0, g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x) ∧
    (∫ x in Set.Ici 0, x * g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x) =
        ∫ x in Set.Icc 0 tau, x * g x := by
  have hindm : Measurable ((Set.Iic tau).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Iic
  have hind : ∀ x, 0 ≤ x → (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x ∈ Set.Icc (0:ℝ) 1 := by
    intro x _
    by_cases hx : x ∈ Set.Iic tau <;> simp [hx]
  have p2 : (∫ x in Set.Icc 0 tau, g x) ≤
      (∫ x in Set.Ici 0, g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x) :=
    (ind_int tau g).symm.le
  have p3 := ind_int tau (fun x => x * g x)
  refine ⟨⟨⟨_, hindm, hind, p2, p3.symm⟩, ?_⟩, p2, p3⟩
  rintro v ⟨γ, hγm, hγ, hc, rfl⟩
  by_cases hτ : 0 ≤ tau
  · have i1 := int_mul _ γ hxg_int hγm hγ
    have i2 := int_mul _ _ hxg_int hindm hind
    have i3 := int_mul _ γ hg_int hγm hγ
    have i4 := int_mul _ _ hg_int hindm hind
    have key : 0 ≤ ∫ x in Set.Ici 0,
        ((x * g x * γ x - x * g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x) -
          tau * (g x * γ x - g x * (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x)) := by
      apply setIntegral_nonneg measurableSet_Ici
      intro x hx
      have hx0 : 0 ≤ x := hx
      obtain ⟨h0, h1⟩ := hγ x hx0
      have hgx := hg x
      by_cases hxt : x ≤ tau
      · have e : (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x = 1 := by
          simp [Set.indicator, hxt]
        rw [e]
        nlinarith [mul_nonneg (mul_nonneg hgx (sub_nonneg.2 h1)) (sub_nonneg.2 hxt)]
      · have e : (Set.Iic tau).indicator (fun _ => (1 : ℝ)) x = 0 := by
          simp [Set.indicator, hxt]
        rw [e]
        push Not at hxt
        nlinarith [mul_nonneg (mul_nonneg hgx h0) (sub_nonneg.2 hxt.le)]
    rw [integral_sub, integral_sub, integral_const_mul, integral_sub, p3, ind_int tau g] at key
    · nlinarith [mul_nonneg hτ (sub_nonneg.2 hc)]
    all_goals first | exact i1 | exact i2 | exact i3 | exact i4 | exact i1.sub i2 | exact (i3.sub i4).const_mul tau
  · push Not at hτ
    rw [Set.Icc_eq_empty (by linarith : ¬ (0:ℝ) ≤ tau), Measure.restrict_empty, integral_zero_measure]
    apply setIntegral_nonneg measurableSet_Ici
    intro x hx
    exact mul_nonneg (mul_nonneg hx (hg x)) (hγ x hx).1
