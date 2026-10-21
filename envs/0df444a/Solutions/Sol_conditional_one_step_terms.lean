-- Prove2me | solution 1 for conditional_one_step_terms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T01:42:13.832233+00:00
-- url     : https://prove2.me/submissions/9c004beb-9ead-4f97-af4a-e1c8224eb165

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Theorems.Thm_stochIter_measurable_of_stronglyMeasurable
import Theorems.Thm_condExp_add_lam_g
import Theorems.Thm_condExp_sub_lam_g
import Theorems.Thm_condExp_mul_lam_g
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Topology
open scoped InnerProductSpace
open ShorNonsmooth.Stochastic
theorem solution {n : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    (h : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (hh_meas : ∀ j, Measurable (h j))
    (G : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (xstar : EuclideanSpace ℝ (Fin n)) (B : ℝ)
    (hh_pos : ∀ y, 0 < h k y) (hh_bdd : ∀ y, h k y ≤ B)
    (hG_int : Integrable (G k) μ) (hG_sq_int : Integrable (fun ω => ‖G k ω‖ ^ 2) μ)
    (hx_int : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) μ)
    (hG_meas : ∀ j, StronglyMeasurable[ℱ (j + 1)] (G j))
    (hFil_le : (ℱ k : MeasurableSpace Ω) ≤ m0)
    (hGk_ae : AEStronglyMeasurable[(ℱ k : MeasurableSpace Ω)] (G k) μ)
    (hdx : Measurable[(ℱ k : MeasurableSpace Ω)] (fun ω => stochIter h G x₀ k ω - xstar))
    (hinner : Integrable (fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ) μ)
    (hinner_pull : μ[fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ | ℱ k]
        =ᵐ[μ] fun ω => ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ) :
    μ[fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2 | ℱ k]
        =ᵐ[μ] fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2
          - 2 * (h k (stochIter h G x₀ k ω)
              * ⟪stochIter h G x₀ k ω - xstar, (μ[G k | ℱ k]) ω⟫_ℝ)
          + (h k (stochIter h G x₀ k ω)) ^ 2
            * (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω := by
  have hstep : ∀ ω, stochIter h G x₀ (k + 1) ω
      = stochIter h G x₀ k ω - h k (stochIter h G x₀ k ω) • G k ω := by
    intro ω; simp [stochIter]
  letI hifm : IsFiniteMeasure μ := inferInstance
  letI hifm' : IsFiniteMeasure (μ.trim hFil_le) := MeasureTheory.isFiniteMeasure_trim hFil_le
  have hxk_fil : Measurable[(ℱ k : MeasurableSpace Ω)] (stochIter h G x₀ k) :=
    stochIter_measurable_of_stronglyMeasurable ℱ h hh_meas G x₀ hG_meas k
  have hH_ae' : AEStronglyMeasurable[(ℱ k : MeasurableSpace Ω)]
      (fun ω => h k (stochIter h G x₀ k ω)) μ := (continuous_id.comp_stronglyMeasurable
      (Measurable.stronglyMeasurable ((hh_meas k).comp hxk_fil))).aestronglyMeasurable
  have hH_ae'' : AEStronglyMeasurable (fun ω => h k (stochIter h G x₀ k ω)) μ :=
    AEStronglyMeasurable.mono hFil_le hH_ae'
  have hA_sm : StronglyMeasurable[(ℱ k : MeasurableSpace Ω)]
      (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2) := (continuous_norm.comp_stronglyMeasurable
      (Measurable.stronglyMeasurable hdx)).pow 2
  have hexp : ∀ ω, ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2
      = ‖stochIter h G x₀ k ω - xstar‖ ^ 2 - 2 * (h k (stochIter h G x₀ k ω)
            * ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ)
        + (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2 := by
    intro ω; rw [hstep ω]
    have hb : h k (stochIter h G x₀ k ω) ≥ 0 := le_of_lt (hh_pos _)
    rw [show stochIter h G x₀ k ω - h k (stochIter h G x₀ k ω) • G k ω - xstar
        = (stochIter h G x₀ k ω - xstar) - h k (stochIter h G x₀ k ω) • G k ω by abel]
    rw [norm_sub_sq_real, real_inner_smul_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have hinterHC : Integrable (fun ω => h k (stochIter h G x₀ k ω)
      * ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ) μ := Integrable.bdd_mul hinner hH_ae'' (by
      filter_upwards with ω
      have hnonneg : 0 ≤ h k (stochIter h G x₀ k ω) := le_of_lt (hh_pos _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]; exact hh_bdd _)
  have hH2_bdd : ∀ᵐ ω ∂μ, ‖(h k (stochIter h G x₀ k ω)) ^ 2‖ ≤ B ^ 2 := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hnonneg : 0 ≤ h k (stochIter h G x₀ k ω) := le_of_lt (hh_pos _)
    have hbdd : h k (stochIter h G x₀ k ω) ≤ B := hh_bdd _
    nlinarith [sq_nonneg (h k (stochIter h G x₀ k ω)), sq_nonneg B]
  have hH2_ae : AEStronglyMeasurable (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2) μ := hH_ae''.pow 2
  have hH2_ae' : AEStronglyMeasurable[(ℱ k : MeasurableSpace Ω)]
      (fun ω => 2 * h k (stochIter h G x₀ k ω)) μ := hH_ae'.const_mul 2
  have hinterQ : Integrable (fun ω => (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2) μ := by
    have h1 : Integrable (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2 * (‖G k ω‖ ^ 2)) μ :=
      Integrable.bdd_mul hG_sq_int hH2_ae hH2_bdd
    have heq : (fun ω => (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2)
        = (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2 * (‖G k ω‖ ^ 2)) := by
      funext ω; ring
    rw [heq]; exact h1
  have hceA : μ[fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 | ℱ k]
      =ᵐ[μ] fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 := by
    have heq : μ[fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 | ℱ k]
        = fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2 := condExp_of_stronglyMeasurable hFil_le hA_sm hx_int
    filter_upwards with ω; exact congrArg (fun g => g ω) heq
  have hceQ : μ[fun ω => (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2 | ℱ k]
      =ᵐ[μ] fun ω => (h k (stochIter h G x₀ k ω)) ^ 2
        * (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]) ω := by
    have hinterQ' : Integrable (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2 * (‖G k ω‖ ^ 2)) μ :=
      Integrable.bdd_mul hG_sq_int hH2_ae hH2_bdd
    have hmul := condExp_mul_lam_g (m := (ℱ k : MeasurableSpace Ω)) (m₀ := m0)
      (f := fun ω => (h k (stochIter h G x₀ k ω)) ^ 2)
      (g := fun ω => ‖G k ω‖ ^ 2)
      (hH_ae'.pow 2) hinterQ' hG_sq_int
    have hconv : (fun ω => (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2)
        =ᵐ[μ] (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2 * (‖G k ω‖) ^ 2) :=
      Filter.EventuallyEq.of_eq (funext fun ω => by rw [mul_pow])
    have h1 := condExp_congr_ae (m := (ℱ k : MeasurableSpace Ω)) (m₀ := m0) hconv
    have h2 : (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2)
        * μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k]
        =ᵐ[μ] fun ω => (h k (stochIter h G x₀ k ω)) ^ 2
          * (μ[fun ω' => ‖G k ω'‖ ^ 2 | ℱ k] ω) := Filter.EventuallyEq.of_eq (by funext ω; rfl)
    exact (h1.trans hmul).trans h2
  have hshape : (fun ω => ‖stochIter h G x₀ (k + 1) ω - xstar‖ ^ 2)
      = (fun ω => ((‖stochIter h G x₀ k ω - xstar‖ ^ 2
          + (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2)
        - (2 * h k (stochIter h G x₀ k ω))
          * ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ)) := by
    funext ω; rw [hexp ω]; ring
  have hsqform : (fun ω => (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2)
      = (fun ω => (h k (stochIter h G x₀ k ω)) ^ 2 * (‖G k ω‖ ^ 2)) := by
    funext ω; rw [mul_pow]
  rw [hshape]
  have hinterAC : Integrable (fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2
      + (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2) μ := hx_int.add hinterQ
  have hinterD : Integrable (fun ω => (2 * h k (stochIter h G x₀ k ω))
      * ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ) μ := by
    have h1 : Integrable (fun ω => 2 * (h k (stochIter h G x₀ k ω)
        * ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ)) μ := hinterHC.const_mul 2
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1
  have hsubACD := condExp_sub_lam_g (m := (ℱ k : MeasurableSpace Ω)) (m₀ := m0)
    (f := fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2
        + (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2)
    (g := fun ω => (2 * h k (stochIter h G x₀ k ω))
        * ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ)
    hinterAC hinterD
  have hsubAC := condExp_add_lam_g (m := (ℱ k : MeasurableSpace Ω)) (m₀ := m0)
    (f := fun ω => ‖stochIter h G x₀ k ω - xstar‖ ^ 2)
    (g := fun ω => (h k (stochIter h G x₀ k ω) * ‖G k ω‖) ^ 2) hx_int hinterQ
  have hsubD := condExp_mul_lam_g (m := (ℱ k : MeasurableSpace Ω)) (m₀ := m0)
    (f := fun ω => 2 * h k (stochIter h G x₀ k ω))
    (g := fun ω => ⟪stochIter h G x₀ k ω - xstar, G k ω⟫_ℝ)
    hH2_ae' hinterD hinner
  filter_upwards [hsubACD, hsubAC, hsubD, hceA, hceQ, hinner_pull]
    with ω hω1 hω2 hω3 hω4 hω5 hω6
  rw [Pi.mul_apply] at hω3
  rw [Pi.add_apply] at hω2
  rw [Pi.sub_apply] at hω1
  rw [hω6] at hω3
  rw [hω4] at hω2
  rw [hω5] at hω2
  rw [hω2] at hω1
  rw [hω3] at hω1
  rw [hω1]
  ring
