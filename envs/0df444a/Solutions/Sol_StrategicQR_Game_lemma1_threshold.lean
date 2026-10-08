-- Prove2me | solution 1 for StrategicQR.Game.lemma1_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:41:09.229205+00:00
-- url     : https://prove2.me/submissions/4edf32ee-0250-4ded-afcc-818ef8dd8582

import Mathlib
import Definitions.Def_StrategicQR_Game_Equilibrium

set_option autoImplicit false

open MeasureTheory in
theorem adf1f83b_psi_props (b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc 0 b)ᶜ = 0) :
    Continuous (fun w : ℝ => ∫ s, max (w - s) 0 ∂μ) ∧
    Monotone (fun w : ℝ => ∫ s, max (w - s) 0 ∂μ) := by
  have hae : ∀ᵐ s ∂μ, s ∈ Set.Icc 0 b := by
    rw [ae_iff]; exact hμ
  have hr : μ.restrict (Set.Icc 0 b) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have heq : (fun w : ℝ => ∫ s, max (w - s) 0 ∂μ) =
      fun w => ∫ s in Set.Icc 0 b, max (w - s) 0 ∂μ := by
    funext w; rw [hr]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  · intro w w' hww'
    have hint : Integrable (fun s : ℝ => max (w' - s) 0) μ := by
      have h : IntegrableOn (fun s : ℝ => max (w' - s) 0) (Set.Icc 0 b) μ :=
        (by fun_prop : Continuous (fun s : ℝ => max (w' - s) 0)).integrableOn_Icc
      rw [IntegrableOn, hr] at h
      exact h
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun s => le_max_right _ _)
    · exact hint
    · exact Filter.Eventually.of_forall (fun s => max_le_max (by linarith) le_rfl)

open StrategicQR.Game MeasureTheory in
theorem solution (M : Model) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Icc 0 M.p)ᶜ = 0) :
    ∃ v ∈ Set.Icc M.vlo M.vhi,
      (∀ w ∈ Set.Ico M.vlo v, ∫ s, max (w - s) 0 ∂μ ≤ M.vM - M.p) ∧
      (∀ w ∈ Set.Ioc v M.vhi, M.vM - M.p ≤ ∫ s, max (w - s) 0 ∂μ) ∧
      (M.vlo < v → v < M.vhi → ∫ s, max (v - s) 0 ∂μ = M.vM - M.p) := by
  obtain ⟨hc, hm⟩ := adf1f83b_psi_props M.p μ hμ
  have hlh := M.vlo_lt_vhi
  by_cases h1 : (fun w : ℝ => ∫ s, max (w - s) 0 ∂μ) M.vhi ≤ M.vM - M.p
  · refine ⟨M.vhi, ⟨hlh.le, le_rfl⟩, ?_, ?_, ?_⟩
    · intro w hw; exact (hm hw.2.le).trans h1
    · intro w hw; exact absurd hw.2 (not_le.mpr hw.1)
    · intro _ h; exact absurd h (lt_irrefl _)
  by_cases h2 : M.vM - M.p ≤ (fun w : ℝ => ∫ s, max (w - s) 0 ∂μ) M.vlo
  · refine ⟨M.vlo, ⟨le_rfl, hlh.le⟩, ?_, ?_, ?_⟩
    · intro w hw; exact absurd hw.2 (not_lt.mpr hw.1)
    · intro w hw; exact h2.trans (hm hw.1.le)
    · intro h; exact absurd h (lt_irrefl _)
  push Not at h1 h2
  obtain ⟨v, hv, hvv⟩ := intermediate_value_Icc hlh.le hc.continuousOn ⟨h2.le, h1.le⟩
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro w hw; rw [← hvv]; exact hm hw.2.le
  · intro w hw; rw [← hvv]; exact hm hw.1.le
  · intro _ _; exact hvv
