-- Prove2me | solution 1 for PDScenRed.Mean.integral_zsel_reflect
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:15:39.177352+00:00
-- url     : https://prove2.me/submissions/830a1395-5159-4769-b2b8-bf2316bf5f58

import Mathlib
import Definitions.Def_PDScenRed_Mean_Setting

set_option autoImplicit false
open scoped InnerProductSpace
open MeasureTheory PDScenRed.Mean

theorem solution {d r : ℕ} (P : Matrix (Fin r) (Fin d) ℝ) (qv : Fin r → ℝ)
    (hne : (polytope P qv).Nonempty) (hbdd : Bornology.IsBounded (polytope P qv))
    (zsel : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hsel : ∀ ξ, zsel ξ ∈ SmartPTO.Fisher.Wstar (polytope P qv) ξ) (hmeas : Measurable zsel)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (hint : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ξ) μ)
    (hsym : SmartPTO.Fisher.CentrallySymmetric μ) :
    ∫ ξ, zsel ((2 : ℝ) • (∫ x, x ∂μ) - ξ) ∂μ = ∫ ξ, zsel ξ ∂μ := by
  have hφ : Measurable (fun c : EuclideanSpace ℝ (Fin d) => (2 : ℝ) • (∫ c', c' ∂μ) - c) :=
    measurable_const.sub measurable_id
  have h := integral_map (μ := μ) hφ.aemeasurable (f := zsel) hmeas.aestronglyMeasurable
  have hs : μ.map (fun c : EuclideanSpace ℝ (Fin d) => (2 : ℝ) • (∫ c', c' ∂μ) - c) = μ := hsym
  rw [hs] at h
  exact h.symm
