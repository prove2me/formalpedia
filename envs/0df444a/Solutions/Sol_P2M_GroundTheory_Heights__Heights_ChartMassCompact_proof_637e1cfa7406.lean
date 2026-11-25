-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMassCompact_proof_637e1cfa7406
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:53.437654+00:00
-- url     : https://prove2.me/submissions/cada217c-a876-4f31-b978-4275958e2480

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_maDens_eq_zero_b0bdbfb94594
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_integrable_ball_09c7bd6a1abc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMassCompact_chartAbsDens_le_567434bbc6d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CutOff_proof_fa25535eea0a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_isClosed_zeroSet_b1e5ce62660e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7


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
open scoped ENNReal
noncomputable section
open ChartMassCompact
namespace GroundTheory.Heights₂.Heights
namespace ChartMassCompact
theorem _root_.solution (hC : ChartMassCompare.Statement) (hMF : MassFinite.Statement) :
    ChartMassCompact.Statement := by
  classical
  intro n d J A f ψ hJ hd hA hf hψ hsupp
  obtain ⟨K, hKc, hvan⟩ : ∃ K : Set (Fin n → ℂ), IsCompact K ∧ ∀ x s, IsSheetAt J A x s → x ∉ K →
      f x * ReciprocityTheory.AnForm.maDens (fun k => ψ k ∘ s) (A *ᵥ x) = 0 := by
    rcases hsupp with hc | ⟨i, hc⟩
    · exact ⟨tsupport f, hc, fun x s _ hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]⟩
    · exact ⟨tsupport (ψ i), hc, fun x s hs hx => by rw [maDens_eq_zero hs ψ i hx, mul_zero]⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKc.isBounded
  obtain ⟨M, hM⟩ := (hKc.inter_left (SheetSumMeasurable.isClosed_zeroSet J)).exists_bound_of_continuousOn
    (hf.mono Set.inter_subset_left)
  have heq : chartAbsDens J A f ψ = chartAbsDens J A ((zeroSet J).piecewise f 0) ψ := by
    funext y
    unfold chartAbsDens sheetSum
    refine finsum_congr fun x => finsum_congr fun hx => ?_
    simp only [Set.piecewise_eq_of_mem _ _ _ hx.1]
  have hgm : Measurable ((zeroSet J).piecewise f 0) :=
    hf.measurable_piecewise continuousOn_const (SheetSumMeasurable.isClosed_zeroSet J).measurableSet
  have hmeas : AEStronglyMeasurable (chartAbsDens J A f ψ) volume := by
    rw [heq]
    exact (SheetSumMeasurable.proof n d J A _ ψ hJ hd hA hgm hψ).2.aestronglyMeasurable
  refine ((integrable_ball hC hMF J A ψ hJ hd hA hψ R).const_mul (max M 0)).mono' hmeas
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  exact chartAbsDens_le J A f ψ hR (fun x hx => (Real.norm_eq_abs (f x) ▸ hM x hx).trans (le_max_left _ _))
    (le_max_right _ _) hvan y (FibreBound.proof n d J A hJ hd hA y).2.1
end ChartMassCompact
end GroundTheory.Heights₂.Heights
