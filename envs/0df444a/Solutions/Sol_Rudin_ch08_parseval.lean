-- Prove2me | solution 1 for Rudin.ch08_parseval
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T12:40:45.943468+00:00
-- url     : https://prove2.me/submissions/c5a90965-f0bb-4eeb-9d74-b4a36180932d

import Mathlib
import Definitions.Def_Rudin_ch08_fourier
import Theorems.Thm_Rudin_ch08_parseval_L2_conv
import Theorems.Thm_Rudin_ch08_parseval_inner
import Theorems.Thm_Rudin_ch08_parseval_norm

open Filter Topology

theorem solution (f g : ℝ → ℂ) (hfper : Rudin.HasPeriodTwoPi f) (hgper : Rudin.HasPeriodTwoPi g)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi)
    (hg2 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => Rudin.L2Norm (fun x => f x - Rudin.fourierPartialSum f N x)) atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        Rudin.fourierCoeff f n * (starRingEnd ℂ) (Rudin.fourierCoeff g n)) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x))) ∧
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖Rudin.fourierCoeff f n‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2)) := by
  exact ⟨Rudin.ch08_parseval_L2_conv f hfper hf hf2,
         Rudin.ch08_parseval_inner f g hfper hgper hf hg hf2 hg2,
         Rudin.ch08_parseval_norm f hfper hf hf2⟩
