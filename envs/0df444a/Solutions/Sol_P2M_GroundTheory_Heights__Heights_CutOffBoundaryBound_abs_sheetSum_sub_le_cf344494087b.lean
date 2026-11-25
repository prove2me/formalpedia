-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CutOffBoundaryBound_abs_sheetSum_sub_le_cf344494087b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:28:25.699204+00:00
-- url     : https://prove2.me/submissions/da13a1bb-dfd1-4edc-8ed2-03a09f032fa6

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
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite)
    (T₁ T₂ P Q₁ Q₂ R₁ R₂ : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (a b c : ℝ)
    (h : ∀ x ∈ fibre J A y, ∀ s, IsSheetAt J A x s →
      |T₁ x s - T₂ x s| ≤ a * P x s + b * (Q₁ x s - Q₂ x s) + c * (R₁ x s - R₂ x s)) :
    |sheetSum J A T₁ y - sheetSum J A T₂ y| ≤ a * sheetSum J A P y +
      b * (sheetSum J A Q₁ y - sheetSum J A Q₂ y) + c * (sheetSum J A R₁ y - sheetSum J A R₂ y) := by
  classical
  unfold sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  split_ifs with hs
  · exact h x hx _ hs.choose_spec
  · simp
end GroundTheory.Heights₂.Heights.CutOffBoundaryBound
