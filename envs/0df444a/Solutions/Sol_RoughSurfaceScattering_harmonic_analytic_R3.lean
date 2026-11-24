-- Prove2me | solution 1 for RoughSurfaceScattering.harmonic_analytic_R3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T06:04:26.213935+00:00
-- url     : https://prove2.me/submissions/c22fb874-326d-4773-b2cc-a941a56be4e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_harmonic_cauchy_estimates_R3
import Theorems.Thm_RoughSurfaceScattering_analyticAt_of_iteratedFDeriv_bound

open MeasureTheory
open RoughSurfaceScattering

theorem solution (f : EuclideanSpace ℝ (Fin 3) → ℂ) (x : EuclideanSpace ℝ (Fin 3))
    (hf : InnerProductSpace.HarmonicAt f x) : AnalyticAt ℝ f x := by
  obtain ⟨R, hR, M, ρ, hρ, hsmooth, hbound⟩ := harmonic_cauchy_estimates_R3 f x hf
  exact analyticAt_of_iteratedFDeriv_bound f x R M ρ hR hρ hsmooth hbound
