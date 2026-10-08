-- Prove2me | solution 1 for TeschlQM.Herglotz.boundary_im_eq_deriv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T22:11:51.694459+00:00
-- url     : https://prove2.me/submissions/348077eb-0aac-42f8-b261-b64c5fd98ebf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TeschlQM_Herglotz_ae_hasMeasureDeriv_rnDeriv
import Theorems.Thm_TeschlQM_Herglotz_ae_hasMeasureDeriv_top_singularPart
import Theorems.Thm_TeschlQM_Herglotz_boundary_im_tendsto_of_hasMeasureDeriv
import Theorems.Thm_TeschlQM_Herglotz_isMinimalSupport_acPart_of_ae_density
import Definitions.Def_TeschlQM_Herglotz_IsSupport
import Definitions.Def_TeschlQM_Herglotz_scPart

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∀ᵐ (t : ℝ) ∂μ, ∃ L : ℝ≥0∞, Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 L)) ∧
    (∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), ∃ L : ℝ≥0∞, Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 L)) ∧
    (∀ (t : ℝ) (d : ℝ≥0∞), HasMeasureDeriv μ t d →
      Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 d)) ∧
    IsSupport (scPart μ) {t : ℝ | Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 ⊤)} ∧
    IsMinimalSupport (acPart μ) {t : ℝ | ∃ L : ℝ≥0∞, 0 < L ∧ L < ⊤ ∧
      Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)) (𝓝[>] (0 : ℝ)) (𝓝 L)} := by
  let g := fun t ε : ℝ => ENNReal.ofReal
    ((borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi)
  have hv := ae_hasMeasureDeriv_rnDeriv μ
  have hs := ae_hasMeasureDeriv_top_singularPart μ
  have hb : ∀ t d, HasMeasureDeriv μ t d → Tendsto (g t) (𝓝[>] (0 : ℝ)) (𝓝 d) :=
    boundary_im_tendsto_of_hasMeasureDeriv μ
  have hvol : ∀ᵐ t ∂(volume : Measure ℝ), ∃ d, HasMeasureDeriv μ t d := by
    filter_upwards [hv] with t ht using ⟨_, ht⟩
  have hac : ∀ᵐ t ∂(acPart μ), ∃ d, HasMeasureDeriv μ t d :=
    (withDensity_absolutelyContinuous volume (μ.rnDeriv volume)).ae_le hvol
  have hmu : ∀ᵐ t ∂μ, ∃ d, HasMeasureDeriv μ t d := by
    have hsum : ∀ᵐ t ∂(μ.singularPart volume + acPart μ),
        ∃ d, HasMeasureDeriv μ t d :=
      ae_add_measure_iff.mpr ⟨hs.mono (fun t ht => ⟨⊤, ht⟩), hac⟩
    simpa only [acPart, Measure.singularPart_add_rnDeriv] using hsum
  refine ⟨?_, ?_, hb, ?_, ?_⟩
  · filter_upwards [hmu] with t ht
    obtain ⟨d, hd⟩ := ht
    exact ⟨d, hb t d hd⟩
  · filter_upwards [hvol] with t ht
    obtain ⟨d, hd⟩ := ht
    exact ⟨d, hb t d hd⟩
  · change (scPart μ) {t | Tendsto (g t) (𝓝[>] (0 : ℝ)) (𝓝 ⊤)}ᶜ = 0
    exact ae_iff.mp ((ae_restrict_of_ae hs).mono (fun t ht => hb t ⊤ ht))
  · apply isMinimalSupport_acPart_of_ae_density
    filter_upwards [hv] with t ht
    constructor
    · rintro ⟨L, hL0, hLfin, hL⟩
      have heq : L = μ.rnDeriv volume t := tendsto_nhds_unique hL (hb t _ ht)
      exact heq ▸ ⟨hL0, hLfin⟩
    · rintro ⟨hpos, hfin⟩
      exact ⟨_, hpos, hfin, hb t _ ht⟩
