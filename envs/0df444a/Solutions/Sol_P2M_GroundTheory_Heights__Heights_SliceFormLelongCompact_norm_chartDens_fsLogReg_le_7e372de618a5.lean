-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_norm_chartDens_fsLogReg_le_7e372de618a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:15.440992+00:00
-- url     : https://prove2.me/submissions/5a89d842-9f02-4800-a18f-e608ab43afd9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_abs_fsLogReg_le_7659ff6b41cf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594
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
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (fsLogReg h u ε) (vecCons f φ) y‖ ≤
      2 * chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · have hb := abs_fsLogReg_le h u x hε hε1 (hy x hx) (h.dualNorm_pos (h0 x hx.1))
      have hpos : (0 : ℝ) ≤ 2 * |Real.log (h.dualNorm x)| + 1 := by positivity
      rw [Set.indicator_of_mem hxB, Real.norm_eq_abs]
      simp only [abs_mul]
      rw [abs_of_nonneg hpos]
      exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (le_of_eq (by ring))
    · have hM := ChartMassCompact.maDens_eq_zero hs.choose_spec (vecCons f φ) 0
        (by simpa using fun h' => hxB (hR h'))
      rw [hx.2] at hM
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
