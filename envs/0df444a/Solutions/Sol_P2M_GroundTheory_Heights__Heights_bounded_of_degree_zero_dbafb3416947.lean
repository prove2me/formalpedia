-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_bounded_of_degree_zero_dbafb3416947
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:25:43.674116+00:00
-- url     : https://prove2.me/submissions/b782fb02-3f57-4810-b0c8-bc0680bdd327

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (g : (Fin n → ℂ) → ℝ)
    (hdeg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x)
    (hc : ContinuousOn g {x | x ≠ 0}) : ∃ B : ℝ, ∀ x, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_bound_of_continuousOn
    (hc.mono fun x hx => by
      rintro rfl
      simp at hx)
  refine ⟨max B |g 0|, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    exact le_max_right _ _
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have hne : ((‖x‖⁻¹ : ℝ) : ℂ) ≠ 0 := by simpa using hn
    rw [← hdeg _ x hne]
    refine le_trans ?_ (le_max_left _ _)
    have hmem : ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ sphere (0 : Fin n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_norm, inv_mul_cancel₀ hn]
    simpa [Real.norm_eq_abs] using hB _ hmem
end GroundTheory.Heights₂.Heights
