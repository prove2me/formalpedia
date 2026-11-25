-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_indicator_0a8753c989df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:51:29.285973+00:00
-- url     : https://prove2.me/submissions/ee00a3b4-7a19-4f66-8014-03438dea6f02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd

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
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntCountAdd
theorem _root_.solution {E : ℕ → Set (Fin n → ℂ)} (hE : Pairwise (Function.onFun Disjoint E))
    (g : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) :
    HasSum (fun i => (E i).indicator g x) ((⋃ i, E i).indicator g x) := by
  by_cases hx : x ∈ ⋃ i, E i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hval : (⋃ i, E i).indicator g x = (E j).indicator g x := by
      simp [Set.indicator_of_mem hx, Set.indicator_of_mem hj]
    rw [hval]
    refine hasSum_single j fun i hi => ?_
    have hxi : x ∉ E i := fun hxi => Set.disjoint_left.1 (hE hi) hxi hj
    simp [hxi]
  · have h0 : ∀ i, (E i).indicator g x = 0 := fun i => by
      have hxi : x ∉ E i := fun h => hx (Set.mem_iUnion.2 ⟨i, h⟩)
      simp [hxi]
    have hu : (⋃ i, E i).indicator g x = 0 := by simp only [Set.indicator_of_notMem hx]
    simp only [h0, hu]
    exact hasSum_zero
end GroundTheory.Heights₂.Heights.ChartIntCountAdd
