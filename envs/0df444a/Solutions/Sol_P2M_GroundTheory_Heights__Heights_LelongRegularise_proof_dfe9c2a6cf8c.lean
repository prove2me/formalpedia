-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LelongRegularise_proof_dfe9c2a6cf8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:43.733798+00:00
-- url     : https://prove2.me/submissions/671ff5b6-1425-4fd9-b4a2-af82aa2f87af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_exists_poly_of_linEval_eq_zero_1a20ed7e007c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_ae_eval_ne_zero_9e323230ff5d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_norm_chartDens_le_7e34c9bb0f45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LelongRegularise_tendsto_chartDens_8eb37c799e78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3


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
namespace GroundTheory.Heights₂.Heights
namespace LelongRegularise
theorem _root_.solution (h : LogIntegrable.Statement) : LelongRegularise.Statement := by
  intro n d J u f φ hJ hdim hu hf hfc hφ
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  have hAf := hA.choose_spec
  unfold chartInt
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hf
    · simpa using hφ i
  have hu2 : linForm ((2 : ℂ) • u) ∉ J := by
    have he : linForm ((2 : ℂ) • u) = C 2 * linForm u := by
      simp [linForm, Finset.mul_sum, ← mul_assoc, C_mul]
    intro hm
    apply hu
    have := J.mul_mem_left (C (1 / 2 : ℂ)) (he ▸ hm)
    rwa [← mul_assoc, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1, one_mul] at this
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hAf hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J hA.choose y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx h0
    exact hy (hPy y x hx h0)
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
    ((h n (d + 1) J hA.choose u (vecCons f φ) R hJ hdim hAf hu hψ).add
      (h n (d + 1) J hA.choose ((2 : ℂ) • u) (vecCons f φ) R hJ hdim hAf hu2 hψ)) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (SheetSumMeasurable.proof n (d + 1) J hA.choose (logReg u ε) (vecCons f φ) hJ hdim hAf
      (contDiff_logReg u hε).continuous.measurable hψ).1.aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hgood] with y hy
    exact LelongRegularise.norm_chartDens_le hAf φ hR hε.1 hε.2 hy
  · filter_upwards [hgood] with y hy
    exact LelongRegularise.tendsto_chartDens hAf _ hy
end LelongRegularise
end GroundTheory.Heights₂.Heights
