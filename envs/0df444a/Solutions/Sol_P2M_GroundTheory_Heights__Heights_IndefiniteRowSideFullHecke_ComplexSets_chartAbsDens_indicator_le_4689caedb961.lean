-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_chartAbsDens_indicator_le_4689caedb961
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:56:26.989283+00:00
-- url     : https://prove2.me/submissions/d08ac628-dd0d-4606-bf6b-52c661da728d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_EqZeroOfMemZeroLocusLineOriginIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GraphChartEventuallyEqSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsSheetMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_fibre_finite_20785c71949c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial MeasureTheory Filter
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (l : (Fin n → ℂ) → ℝ) {B C : Set (Fin n → ℂ)} (hBC : B ⊆ C)
    (y : Fin d → ℂ) :
    0 ≤ GroundTheory.Heights₂.Heights.chartAbsDens J A (B.indicator l) φ y ∧
      GroundTheory.Heights₂.Heights.chartAbsDens J A (B.indicator l) φ y ≤
        GroundTheory.Heights₂.Heights.chartAbsDens J A (C.indicator l) φ y := by
  unfold GroundTheory.Heights₂.Heights.chartAbsDens GroundTheory.Heights₂.Heights.sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (fibre_finite hA y)]
  refine ⟨Finset.sum_nonneg fun x _ => ?_, Finset.sum_le_sum fun x _ => ?_⟩
  · split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  · split_ifs
    · dsimp only
      rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hBC hx)]
      · rw [Set.indicator_of_notMem hx, abs_zero]
        exact abs_nonneg _
    · exact le_rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
