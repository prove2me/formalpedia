-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_fracPairs_div_c2105d6455a7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:58:43.351972+00:00
-- url     : https://prove2.me/submissions/028b6920-10be-4ac8-98a2-728735cbe593

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution {c c' : (Σ k, ι k) → Φ} {p p' : Φ} (hp : (p, p) ∈ fracPairs c c')
    (hp' : (p', p') ∈ fracPairs c c') (h0 : p' ≠ 0) : (p / p', p / p') ∈ fracPairs c c' := by
  obtain ⟨γ₁, r₁, q₁, hr₁, hq₁, h₁, h₁', e₁, e₁'⟩ := hp
  obtain ⟨γ₂, r₂, q₂, hr₂, hq₂, h₂, h₂', e₂, e₂'⟩ := hp'
  refine ⟨γ₁ + γ₂, r₁ * q₂, q₁ * r₂, exHomog_mul hr₁ hq₂, exHomog_mul hq₁ hr₂, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, e₂]
    exact mul_ne_zero h₁ (mul_ne_zero h₂ h0)
  · rw [map_mul, e₂']
    exact mul_ne_zero h₁' (mul_ne_zero h₂' h0)
  · rw [map_mul, map_mul, e₁, e₂]
    field_simp
  · rw [map_mul, map_mul, e₁', e₂']
    field_simp
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
