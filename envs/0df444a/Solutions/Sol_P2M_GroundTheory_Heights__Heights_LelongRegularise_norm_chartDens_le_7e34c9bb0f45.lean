-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_norm_chartDens_le_7e34c9bb0f45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:10.423984+00:00
-- url     : https://prove2.me/submissions/fc1de8ca-9ae3-4a0b-a411-5661c26c26eb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_maDens_eq_zero_of_eventually_fd74858b873d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_abs_half_log_le_044daed9760d
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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.LelongRegularise
namespace GroundTheory.Heights₂.Heights.LelongRegularise
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (logReg u ε) (vecCons f φ) y‖ ≤
      chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval ((2 : ℂ) • u) x‖)
          (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_mul, ← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h2 : ‖linEval ((2 : ℂ) • u) x‖ = 2 * ‖linEval u x‖ := by
        have : linEval ((2 : ℂ) • u) x = 2 * linEval u x := by
          simp [linEval, Finset.mul_sum, mul_assoc]
        rw [this, norm_mul]
        norm_num
      rw [h2]
      exact abs_half_log_le (norm_pos_iff.2 (hy x hx)) hε hε1
    · have hM : ReciprocityTheory.AnForm.maDens (fun k => vecCons f φ k ∘ hs.choose) y = 0 := by
        obtain ⟨U, hU, hxU, hsd, hsx, -⟩ := hs.choose_spec
        refine maDens_eq_zero_of_eventually _ ?_
        have hc : ContinuousAt hs.choose y := by
          rw [← hx.2]
          exact hsd.continuousOn.continuousAt (hU.mem_nhds hxU)
        have hx' : x ∉ tsupport f := fun h => hxB (hR h)
        have hn : (tsupport f)ᶜ ∈ 𝓝 (hs.choose y) := by
          rw [← hx.2, hsx]
          exact (isClosed_tsupport f).isOpen_compl.mem_nhds hx'
        filter_upwards [hc.preimage_mem_nhds hn] with w hw
        simp only [Matrix.cons_val_zero, Function.comp_apply]
        exact image_eq_zero_of_notMem_tsupport hw
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp
end GroundTheory.Heights₂.Heights.LelongRegularise
