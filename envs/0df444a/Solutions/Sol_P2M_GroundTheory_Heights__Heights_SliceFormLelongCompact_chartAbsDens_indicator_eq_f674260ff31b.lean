-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_chartAbsDens_indicator_eq_f674260ff31b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:12.953931+00:00
-- url     : https://prove2.me/submissions/4eae3a8a-bd6a-4b4a-8596-45e977ee9ac7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594


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
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {B : Set (Fin n → ℂ)} (i : Fin d)
    (hB : tsupport (ψ i) ⊆ B) : chartAbsDens J A (B.indicator w) ψ = chartAbsDens J A w ψ := by
  funext y
  unfold chartAbsDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  split_ifs with hs
  · by_cases hxB : x ∈ B
    · dsimp only
      rw [Set.indicator_of_mem hxB]
    · have hM := ChartMassCompact.maDens_eq_zero hs.choose_spec ψ i fun h => hxB (hB h)
      rw [hx.2] at hM
      simp [hM]
  · rfl
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
