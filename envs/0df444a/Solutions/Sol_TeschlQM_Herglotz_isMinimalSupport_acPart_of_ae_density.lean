-- Prove2me | solution 1 for TeschlQM.Herglotz.isMinimalSupport_acPart_of_ae_density
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T22:08:34.196277+00:00
-- url     : https://prove2.me/submissions/9da1ea9e-0282-4334-a437-62991dacdb46

import Definitions.Def_TeschlQM_Herglotz_acPart
import Definitions.Def_TeschlQM_Herglotz_IsMinimalSupport

open MeasureTheory Filter
open scoped ENNReal Topology
open TeschlQM.Herglotz

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ] (S : Set ℝ)
    (hS : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ S ↔ 0 < μ.rnDeriv volume t ∧ μ.rnDeriv volume t < ⊤) :
    IsMinimalSupport (acPart μ) S := by
  constructor
  · change (volume.withDensity (μ.rnDeriv volume)) Sᶜ = 0
    have hmem : ∀ᵐ t ∂volume.withDensity (μ.rnDeriv volume), t ∈ S := by
      apply (ae_withDensity_iff (Measure.measurable_rnDeriv μ volume)).2
      filter_upwards [hS, μ.rnDeriv_lt_top volume] with t ht hfin hpos
      exact (ht.mpr ⟨pos_iff_ne_zero.mpr hpos, hfin⟩)
    exact ae_iff.mp hmem
  · intro M hM hsub hnull
    have hn : ∀ᵐ t ∂(acPart μ), t ∉ M := by
      rw [ae_iff]
      simpa using hnull
    have hz := (ae_withDensity_iff (Measure.measurable_rnDeriv μ volume)).1 hn
    have hnot : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ M := by
      filter_upwards [hS, hz] with t ht hzt
      intro hm
      exact hzt (ht.mp (hsub hm)).1.ne' hm
    simpa using ae_iff.mp hnot
