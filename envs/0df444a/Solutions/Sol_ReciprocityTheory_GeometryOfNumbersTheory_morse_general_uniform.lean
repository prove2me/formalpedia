-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morse_general_uniform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:21:02.727516+00:00
-- url     : https://prove2.me/submissions/7936e8e9-3ccb-4d68-93a6-a150b08c73a5

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseGenSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_morseGen_uniform


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Complex Matrix
open scoped ComplexOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (ρ₀ K₂ K₃ Lν νmin : ℝ) (hρ₀ : 0 < ρ₀) (hνmin : 0 < νmin) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ (φ ν : (Fin D → ℂ) → ℝ) (f : (Fin D → ℂ) → ℂ),
      ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀) →
      ‖fderiv ℝ (fderiv ℝ φ) 0‖ ≤ K₂ →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃) →
      ContinuousOn ν (Metric.ball 0 ρ₀) → νmin ≤ ν 0 →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ν 0 - Lν * ‖z‖ ≤ ν z) →
      (∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 0 ≤ ν z) →
      DifferentiableOn ℂ f (Metric.ball 0 ρ₀) →
      IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
        (Metric.ball (0 : Fin D → ℂ) ρ₀) →
      ‖f 0‖ ^ 2 * Real.exp (-((n : ℝ) * φ 0)) ≤ M * (n : ℝ) ^ D *
        ∫ z in Metric.ball (0 : Fin D → ℂ) ρ₀, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
  exact morseGen_uniform hρ₀ hνmin
end ReciprocityTheory.GeometryOfNumbersTheory
