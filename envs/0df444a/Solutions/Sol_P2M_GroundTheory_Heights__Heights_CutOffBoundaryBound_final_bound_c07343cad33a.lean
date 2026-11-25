-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_final_bound_c07343cad33a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:20.311818+00:00
-- url     : https://prove2.me/submissions/51d076ec-b6da-47db-aa08-42f4b8affaac

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
theorem _root_.solution {X M C aI E Φ : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ aI)
    (h : ∀ t > 0, X ≤ M * aI + C * t * E + C / t * Φ) :
    X ≤ max M (2 * C * √(max Φ 1)) * (aI + √E) := by
  have hΦ1 : 0 < max Φ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hv : 0 < √(max Φ 1) := Real.sqrt_pos.2 hΦ1
  have hΦ2 : max Φ 1 = √(max Φ 1) ^ 2 := (Real.sq_sqrt hΦ1.le).symm
  rcases le_or_gt E 0 with hE | hE
  · rw [Real.sqrt_eq_zero'.2 hE, add_zero]
    have hX : X ≤ M * aI := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have ht : 0 < (C * max Φ 1 + 1) / ε := by positivity
      have h0 := h _ ht
      have h1 : C * ((C * max Φ 1 + 1) / ε) * E ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hE
      have h2 : C / ((C * max Φ 1 + 1) / ε) * Φ ≤ C / ((C * max Φ 1 + 1) / ε) * max Φ 1 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      have h3 : C / ((C * max Φ 1 + 1) / ε) * max Φ 1 ≤ ε := by
        rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hC hΦ1.le]
      linarith
    exact hX.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
  · have hu : 0 < √E := Real.sqrt_pos.2 hE
    have hE2 : E = √E ^ 2 := (Real.sq_sqrt hE.le).symm
    have h0 := h (√(max Φ 1) / √E) (by positivity)
    have h1 : C * (√(max Φ 1) / √E) * E = C * √E * √(max Φ 1) := by
      rw [hE2, Real.sqrt_sq hu.le]
      field_simp
    have h2 : C / (√(max Φ 1) / √E) * Φ ≤ C * √E * √(max Φ 1) := by
      calc C / (√(max Φ 1) / √E) * Φ ≤ C / (√(max Φ 1) / √E) * max Φ 1 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        _ = C * √E * √(max Φ 1) := by
            rw [hΦ2, Real.sqrt_sq hv.le]
            field_simp
    calc X ≤ M * aI + (2 * C * √(max Φ 1)) * √E := by linarith
      _ ≤ max M (2 * C * √(max Φ 1)) * aI + max M (2 * C * √(max Φ 1)) * √E :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ha)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hu.le)
      _ = max M (2 * C * √(max Φ 1)) * (aI + √E) := by ring
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
