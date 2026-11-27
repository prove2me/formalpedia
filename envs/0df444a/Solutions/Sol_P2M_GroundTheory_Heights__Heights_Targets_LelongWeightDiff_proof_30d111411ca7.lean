-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_proof_30d111411ca7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:10.766084+00:00
-- url     : https://prove2.me/submissions/74a8c8a7-8122-4653-867d-ebac0bb7f55a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_ae_eval_ne_zero_80133a975faf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_proof_e9b099c76968
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOffDominated_sheetSum_eq_sum_7191afe3cbd4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_ae_eval_ne_zero_e1e014cbbf7d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_chartDens_le_d540820e7c5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_abs_half_log_sub_le_d0d8b9aa61fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_chartDens_sub_34a67d38934d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_exists_poly_of_linEval_eq_zero_7478f6dc9d62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_measurable_chartDens_039b8fbc9b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_tendsto_finset_sum_zero_a6939454619a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_linEval_b27409562f54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
namespace GroundTheory.Heights₂.Heights.Targets
namespace LelongWeightDiff
theorem _root_.solution (hM : ChartMassCompact.Statement) : LelongWeightDiff.Statement := by
  classical
  intro n d J u g k φ hJ hdim hu hg hgc hφ hk hkpos
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons g φ i) := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (⟨Set.univ, isOpen_univ, Set.subset_univ _, hg.contDiffOn⟩ : SmoothNear (zeroSet J) g)
    · simpa using hφ j
  have hcs : ∃ i, HasCompactSupport (vecCons g φ i) := ⟨0, by simpa using hgc⟩
  by_cases hA : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · simp only [varInt, dif_neg hA, sub_self]; exact tendsto_const_nhds
  simp only [varInt, dif_pos hA]
  set A := hA.choose
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
  have hkc : ContinuousOn k (zeroSet J) := by
    obtain ⟨U, -, hU, hkU⟩ := hk; exact hkU.continuousOn.mono hU
  have hlc : Continuous fun x => ‖linEval u x‖ ^ 2 := ((contDiff_linEval u).continuous.norm).pow 2
  set D : ℝ → (Fin n → ℂ) → ℝ := fun ε x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2 - logReg u ε x
  have hWc : ∀ ε : ℝ, 0 < ε →
      ContinuousOn (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (zeroSet J) := fun ε hε =>
    ((hlc.continuousOn.add (continuousOn_const.mul (hkc.pow 2))).log fun x hx => by
      exact (add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hε (pow_pos (hkpos x hx) 2))).ne').div_const 2
  have hLc : ∀ ε : ℝ, 0 < ε → ContinuousOn (logReg u ε) (zeroSet J) := fun ε hε =>
    (contDiff_logReg u hε).continuous.continuousOn
  have hint : ∀ f, ContinuousOn f (zeroSet J) → Integrable (chartDens J A f (vecCons g φ)) := fun f hf =>
    (hM n (d + 1) J A f _ hJ hdim hAf hf hψ (Or.inr hcs)).mono'
      (LelongWeightDiff.measurable_chartDens hJ hdim hAf hf hψ).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact LelongWeightDiff.abs_chartDens_le _ _ (hfin y))
  have heq : (fun ε : ℝ => ∫ y, chartDens J A (D ε) (vecCons g φ) y) =ᶠ[𝓝[>] 0]
      fun ε => chartInt J A (fun x => Real.log (‖linEval u x‖ ^ 2 + ε * k x ^ 2) / 2) (vecCons g φ) -
        chartInt J A (logReg u ε) (vecCons g φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [chartInt, chartInt, ← integral_sub (hint _ (hWc ε hε)) (hint _ (hLc ε hε))]
    exact integral_congr_ae (Eventually.of_forall fun y =>
      (LelongWeightDiff.chartDens_sub _ _ _ (hfin y)).symm)
  refine Tendsto.congr' heq ?_
  obtain ⟨P, hP0, hPu⟩ := LelongWeightDiff.exists_poly_of_linEval_eq_zero J A hAf u hu
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε => chartDens J A (D ε) (vecCons g φ)) (f := fun _ => (0 : ℝ))
    (chartAbsDens J A (fun x => Real.log (k x)) (vecCons g φ)) ?_ ?_
    (hM n (d + 1) J A _ _ hJ hdim hAf (hkc.log fun x hx => (hkpos x hx).ne') hψ (Or.inr hcs)) ?_
  · rwa [integral_zero] at h
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (LelongWeightDiff.measurable_chartDens hJ hdim hAf ((hWc ε hε).sub (hLc ε hε)) hψ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs
    · rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (LelongWeightDiff.abs_half_log_sub_le (sq_nonneg _) hε (hkpos x hx.1)) (abs_nonneg _)
    · simp
  · filter_upwards [CutOffDominated.ae_eval_ne_zero P hP0] with y hy
    unfold chartDens
    simp only [CutOffDominated.sheetSum_eq_sum _ (hfin y)]
    refine LelongWeightDiff.tendsto_finset_sum_zero _ _ fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    by_cases hs : ∃ s, IsSheetAt J A x s
    swap
    · simp only [dif_neg hs]; exact tendsto_const_nhds
    simp only [dif_pos hs]
    have hux : linEval u x ≠ 0 := fun h0 => hy (by rw [← hx.2]; exact hPu x hx.1 h0)
    have ha : 0 < ‖linEval u x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hux) 2
    have hc : ContinuousAt (fun ε : ℝ => D ε x) 0 := by
      simp only [D, logReg]
      refine ((ContinuousAt.log (by fun_prop) ?_).div_const 2).sub
        ((ContinuousAt.log (by fun_prop) ?_).div_const 2) <;> simp [hux]
    have h0 : D 0 x = 0 := by simp [D, logReg]
    simpa [h0] using ((hc.tendsto.mono_left nhdsWithin_le_nhds).mul_const
      (ReciprocityTheory.AnForm.maDens (fun i => vecCons g φ i ∘ hs.choose) y))
end LelongWeightDiff
end GroundTheory.Heights₂.Heights.Targets
