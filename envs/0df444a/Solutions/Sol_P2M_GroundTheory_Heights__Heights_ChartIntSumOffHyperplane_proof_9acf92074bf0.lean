-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntSumOffHyperplane_proof_9acf92074bf0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:23.683586+00:00
-- url     : https://prove2.me/submissions/db9dc1d9-6a34-4bb8-b5b5-2ceeccb12315

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntSumOffHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartChangeSheetNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntSumOffHyperplane

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
namespace GroundTheory.Heights₂.Heights
namespace ChartIntSumOffHyperplane
theorem _root_.solution (hFB : FibreBound.Statement)
    (hCN : ChartChangeSheetNull.Statement) : ChartIntSumOffHyperplane.Statement := by
  intro n d J A u m f F φ hJ hdim hA hu hf hint

  have hnull := hCN n d J J A A u u Set.univ Set.univ id id hJ hdim hJ hdim hu hu hA hA isOpen_univ
    isOpen_univ (Set.subset_univ _) (Set.subset_univ _) differentiableOn_id differentiableOn_id
    (fun x hx => hx) (fun x hx => hx) (fun x _ => rfl) (fun x _ => rfl)
  have hae : ∀ᵐ y ∂(volume : Measure (Fin d → ℂ)),
      chartDens J A f φ y = ∑ b, chartDens J A (F b) φ y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    have hfin : (fibre J A y).Finite := (hFB n d J A hJ hdim hA y).2.1
    simp only [chartDens, sheetSum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · have hux : linEval u x ≠ 0 := by
        by_contra h0
        exact hy ⟨x, ⟨hx.1, hs, fun h => h.1 h0⟩, hx.2⟩
      rw [hf x hx.1 hux, Finset.sum_mul]
    · simp
  calc chartInt J A f φ = ∫ y, ∑ b, chartDens J A (F b) φ y := integral_congr_ae hae
    _ = ∑ b, chartInt J A (F b) φ := integral_finsetSum _ fun b _ => hint b
end ChartIntSumOffHyperplane
end GroundTheory.Heights₂.Heights
