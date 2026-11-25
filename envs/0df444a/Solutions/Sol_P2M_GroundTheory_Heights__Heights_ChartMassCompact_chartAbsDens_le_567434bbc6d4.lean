-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassCompact_chartAbsDens_le_567434bbc6d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:06.991994+00:00
-- url     : https://prove2.me/submissions/894346a0-ccad-478a-8bb1-8d23116c232b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMassCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMassCompact
theorem _root_.solution (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {K B : Set (Fin n → ℂ)} {M : ℝ}
    (hKB : K ⊆ B) (hM : ∀ x ∈ zeroSet J ∩ K, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hvan : ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0)
    (y : Fin d → ℂ) (hfin : (fibre J A y).Finite) :
    chartAbsDens J A f ψ y ≤ M * chartAbsDens J A (B.indicator fun _ => 1) ψ y := by
  classical
  unfold chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, rfl⟩ := hx
  split_ifs with h
  · dsimp only
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem (hKB hxK), one_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hM x ⟨hxZ, hxK⟩) (abs_nonneg _)
    · rw [hvan x _ h.choose_spec hxK, abs_zero]
      positivity
  · simp
end GroundTheory.Heights₂.Heights.ChartMassCompact
