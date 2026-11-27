-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_proof_5acd17a21aba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:54:21.578231+00:00
-- url     : https://prove2.me/submissions/bc695fcc-e23f-4f05-81e9-4c3abf6d20a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_indicator_0a8753c989df
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_hasSum_sheetSum_5ea7d9e12fbf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_sheetSum_le_1d273918db5b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_sheetSum_mono_8368eee2d608
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_indicator_mul_ac02c5b20e31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_44e467d79ae4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_le_da6dab3ba3ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1


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
open ChartIntCountAdd
namespace GroundTheory.Heights₂.Heights
namespace ChartIntCountAdd
theorem _root_.solution (hCM : ChartMassCompact.Statement) : ChartIntCountAdd.Statement := by
  intro n d W A f φ E hW hdim hA hf hfc hφ hEm hE
  have hfin : ∀ y, (fibre W A y).Finite := fun y =>
    (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
  have hmeas : ∀ g : (Fin n → ℂ) → ℝ, Measurable g →
      Measurable (chartDens W A g φ) ∧ Measurable (chartAbsDens W A g φ) := fun g hg =>
    SheetSumMeasurable.proof n d W A g φ hW hdim hA hg hφ
  have hgm : ∀ i, Measurable ((E i).indicator f) := fun i => hf.measurable.indicator (hEm i)
  have hgu : Measurable ((⋃ i, E i).indicator f) := hf.measurable.indicator (MeasurableSet.iUnion hEm)

  have hdens : ∀ y, HasSum (fun i => chartDens W A ((E i).indicator f) φ y)
      (chartDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [indicator_mul]
    exact hasSum_indicator hE _ x
  have habs : ∀ y, HasSum (fun i => chartAbsDens W A ((E i).indicator f) φ y)
      (chartAbsDens W A ((⋃ i, E i).indicator f) φ y) := by
    intro y
    unfold chartAbsDens
    refine hasSum_sheetSum (hfin y) _ _ fun x s => ?_
    simp only [abs_indicator_mul]
    exact hasSum_indicator hE _ x

  have hdom : Integrable (chartAbsDens W A ((⋃ i, E i).indicator f) φ) := by
    refine (hCM n d W A f φ hW hdim hA hf.continuousOn hφ (Or.inl hfc)).mono'
      (hmeas _ hgu).2.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartAbsDens
    refine (abs_sheetSum_le (hfin y) _).trans (sheetSum_mono (hfin y) fun x s => ?_)
    rw [abs_abs]
    exact abs_indicator_mul_le _ _ _ _
  have hsum : (fun y => ∑' i, chartAbsDens W A ((E i).indicator f) φ y) =
      chartAbsDens W A ((⋃ i, E i).indicator f) φ := funext fun y => (habs y).tsum_eq
  exact hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun i => chartDens W A ((E i).indicator f) φ)
    (f := chartDens W A ((⋃ i, E i).indicator f) φ)
    (fun i => chartAbsDens W A ((E i).indicator f) φ)
    (fun i => (hmeas _ (hgm i)).1.aestronglyMeasurable)
    (fun i => ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]
      exact abs_sheetSum_le (hfin y) _)
    (ae_of_all _ fun y => (habs y).summable)
    (by rw [hsum]; exact hdom)
    (ae_of_all _ hdens)
end ChartIntCountAdd
end GroundTheory.Heights₂.Heights
