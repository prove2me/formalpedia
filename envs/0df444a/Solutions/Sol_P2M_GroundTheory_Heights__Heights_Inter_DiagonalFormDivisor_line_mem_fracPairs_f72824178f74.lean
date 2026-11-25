-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_line_mem_fracPairs_f72824178f74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:39.891671+00:00
-- url     : https://prove2.me/submissions/1b4b3cf1-65ad-401b-b3d4-6906827875f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagFormDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PMobiusAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagFormDiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagonalFormDivisor_mem_fracPairs_of_9d1a77e172f2

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
variable {Ω : Type} [Field Ω] {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
  [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
theorem _root_.solution (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (k₀ k₁ : κ)
    (b₀ b₁ : Φ) (h₀ : T.lineVal e (φ k₀) b₀ ≠ 0) (h₁ : T.lineVal e (φ k₀) b₁ ≠ 0) :
    (T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀, T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀) ∈
        fracPairs (T.wwCoord x δ e φ b₀ b₁) (T.wwCoord x δ e φ b₀ b₀) ∧
      (T.lineVal e (φ k₁) b₁ / T.lineVal e (φ k₀) b₁, T.lineVal e (φ k₁) b₀ / T.lineVal e (φ k₀) b₀) ∈
        fracPairs (T.wwCoord x δ e φ b₀ b₁) (T.wwCoord x δ e φ b₀ b₀) := by
  have hq := exHomog_mul (exHomog_X (ι := T.wwIdx ι ν κ) T.WBlk.line0 k₀) (exHomog_X T.WBlk.line1 k₀)
  constructor
  · refine mem_fracPairs_of (exHomog_mul (exHomog_X T.WBlk.line0 k₁) (exHomog_X T.WBlk.line1 k₀)) hq ?_ ?_ ?_ ?_
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₁
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₀
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
  · refine mem_fracPairs_of (exHomog_mul (exHomog_X T.WBlk.line0 k₀) (exHomog_X T.WBlk.line1 k₁)) hq ?_ ?_ ?_ ?_
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₁
    · simp only [map_mul, aeval_X, T.wwCoord]
      exact mul_ne_zero h₀ h₀
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
    · simp only [map_mul, aeval_X, T.wwCoord]
      field_simp
end GroundTheory.Heights₂.Heights.Inter.DiagonalFormDivisor
