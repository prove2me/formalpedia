-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.exists_pluriharmonic_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:37.776257+00:00
-- url     : https://prove2.me/submissions/4556c0e9-36ec-40fb-95af-0d430acb0246

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_TaylorLeviSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlCx_re
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtlBil_re
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgtl_taylor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Complex
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {ρ₀ K₃ : ℝ} (φ : (Fin D → ℂ) → ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Metric.ball 0 ρ₀))
    (hK₃ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, ‖iteratedFDeriv ℝ 3 φ z‖ ≤ K₃) :
    ∃ q : (Fin D → ℂ) → ℂ, Differentiable ℂ q ∧ q 0 = 0 ∧
      ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀,
        |φ z - φ 0 - (q z).re -
          (fderiv ℝ (fderiv ℝ φ) 0 z z + fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4| ≤
        K₃ * ‖z‖ ^ 3 := by
  refine ⟨fun z => pgtlCx (fderiv ℝ φ 0) z + pgtlBil (fderiv ℝ (fderiv ℝ φ) 0) z z, ?_, ?_, ?_⟩
  · exact (pgtlCx _).differentiable.add ((pgtlBil _).differentiable.clm_apply differentiable_id)
  · simp
  · intro z hz
    have h := pgtl_taylor φ hφ hK₃ z hz
    dsimp only
    rw [add_re, pgtlCx_re, pgtlBil_re]
    have e : φ z - φ 0 - (fderiv ℝ φ 0 z + (fderiv ℝ (fderiv ℝ φ) 0 z z -
        fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4) -
        (fderiv ℝ (fderiv ℝ φ) 0 z z + fderiv ℝ (fderiv ℝ φ) 0 (I • z) (I • z)) / 4 =
        φ z - φ 0 - fderiv ℝ φ 0 z - fderiv ℝ (fderiv ℝ φ) 0 z z / 2 := by ring
    rw [e]
    exact h
end ReciprocityTheory.GeometryOfNumbersTheory
