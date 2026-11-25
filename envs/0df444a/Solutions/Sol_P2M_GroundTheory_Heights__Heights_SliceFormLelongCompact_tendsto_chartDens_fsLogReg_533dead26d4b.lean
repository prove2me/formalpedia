-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_chartDens_fsLogReg_533dead26d4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:43.655556+00:00
-- url     : https://prove2.me/submissions/7170ab41-8416-4be3-a8db-743317743c7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_tendsto_fsLogReg_sub_110b7e07e698
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_dualNorm_pos_3da77c812dcb
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) (u : Fin n → ℂ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {y : Fin d → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (fsLogReg h u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y -
        chartDens J A (fun x => Real.log (h.dualNorm x)) ψ y)) := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib]
  refine tendsto_finsetSum _ fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs, ← sub_mul]
    exact (tendsto_fsLogReg_sub h u x (hy x hx) (h.dualNorm_pos (h0 x hx.1))).mul_const _
  · simp only [dif_neg hs, sub_zero]
    exact tendsto_const_nhds
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
