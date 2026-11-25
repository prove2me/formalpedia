-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_term_bound_3573df0163f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:21.645574+00:00
-- url     : https://prove2.me/submissions/853f0cd7-ceb8-4d2c-8269-f4f7d59f0e44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffBoundaryBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_two_mul_le_add_div_264c0a734aca

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.CutOffBoundaryBound
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.CutOffBoundaryBound
theorem _root_.solution {G F χ mF mχ g₁ g₂ Eχ EF M C t : ℝ} (ht : 0 < t) (hC : 0 ≤ C) (hM : |G * F| ≤ M)
    (hEχ : 0 ≤ Eχ) (hEF : 0 ≤ EF) (h₁ : |g₁| ≤ C * √Eχ * √EF) (h₂ : |g₂| ≤ C * √EF * √Eχ) :
    |G * (χ * mF + F * mχ + g₁ + g₂) - χ * G * mF| ≤
      M * |1 * mχ| + C * t * (1 * Eχ) + C / t * (G ^ 2 * EF) := by
  have key := two_mul_le_add_div ht (√Eχ) (|G| * √EF)
  rw [Real.sq_sqrt hEχ, mul_pow, sq_abs, Real.sq_sqrt hEF] at key
  have hcomm : C * √EF * √Eχ = C * √Eχ * √EF := by ring
  have hsum : |g₁| + |g₂| ≤ 2 * C * (√Eχ * √EF) := by linarith
  calc |G * (χ * mF + F * mχ + g₁ + g₂) - χ * G * mF| = |G * F * mχ + G * (g₁ + g₂)| := by
        congr 1; ring
    _ ≤ |G * F| * |mχ| + |G| * (|g₁| + |g₂|) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_mul _ _).le ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ M * |mχ| + |G| * (2 * C * (√Eχ * √EF)) :=
        add_le_add (mul_le_mul_of_nonneg_right hM (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hsum (abs_nonneg _))
    _ = M * |mχ| + C * (2 * √Eχ * (|G| * √EF)) := by ring
    _ ≤ M * |mχ| + C * (t * Eχ + G ^ 2 * EF / t) := by gcongr
    _ = M * |1 * mχ| + C * t * (1 * Eχ) + C / t * (G ^ 2 * EF) := by rw [one_mul, one_mul]; ring
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
