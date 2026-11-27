-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_proof_bcdd7247332e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:07:35.898924+00:00
-- url     : https://prove2.me/submissions/a0640b9a-bf8c-4ad6-816f-5d0ef098708e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_nhds_99630c412ec0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_sheet_of_det_ne_zero_70cc8ca45db3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_det_ne_zero_bb9babd323db
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CriticalImageNull_proof_bedda1fe3c58
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteMapOpen_proof_223c44725f20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_analyticOnNhd_det_jacC_ddf5e32b96d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_differentiableOn_mulVec_9d66d20ccb40
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_det_ne_zero_9afc28185559
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_nhds_e46767207946
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_sheet_of_det_ne_zero_08ac665d1d09
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_proof_03186e126e60
import Theorems.Thm_ReciprocityTheory_AnForm_volume_eq_zero_of_locally_in_analytic_zero_set


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
namespace RatSheetNoChartNull
theorem _root_.solution : RatSheetNoChartNull.Statement := by
  intro n d J A p q hJ _ hA _
  set B := {x | x ∈ zeroSet J ∧ (∃ s, RatChart.IsRatSheetAt J p q x s) ∧ ¬ ∃ s', IsSheetAt J A x s'}
    with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => RatSheetNoChartNull.exists_sheet_nhds (J := J) (p := p) (q := q) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume (RatChart.ratMap p q '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hRx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hRx
    refine ⟨Metric.ball (RatChart.ratMap p q x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A (hσd i))).mono hball,
      RatSheetNoChartNull.exists_det_ne_zero IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof hJ hA hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (RatSheetNoChartNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩
end RatSheetNoChartNull
end GroundTheory.Heights₂.Heights
