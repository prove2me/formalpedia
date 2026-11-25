-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_chartDens_8eb37c799e78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:59:59.344814+00:00
-- url     : https://prove2.me/submissions/5394b438-9d23-4fec-a282-c45f5e08baeb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_logReg_37400dfe8e65
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
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    (ψ : Fin d → (Fin n → ℂ) → ℝ) {y : Fin d → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (logReg u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y)) := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine tendsto_finsetSum _ fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    exact (tendsto_logReg u x (hy x hx)).mul_const _
  · simp only [dif_neg hs]
    exact tendsto_const_nhds
end GroundTheory.Heights₂.Heights.LelongRegularise
