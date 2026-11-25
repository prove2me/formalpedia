-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_measurableSet_piece_35bf42420ffc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:36.046004+00:00
-- url     : https://prove2.me/submissions/b29ea231-baca-4b2c-8b97-b993d8acb69c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
theorem _root_.solution {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {W : Set X} (hWo : IsOpen W) (hWM : W ⊆ M₀)
    {B : Set (Fin e → ℂ)} (hB : MeasurableSet B) :
    MeasurableSet (((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) ∩
      (q ∘ (A.chart j).symm) ⁻¹' B) := by
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' W with hO
  have hOo : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hWo
  have hc : ContinuousOn (q ∘ (A.chart j).symm) O := fun y hy =>
    (analyticAt_chart j hholo ⟨hy.1, hWM hy.2⟩).continuousAt.continuousWithinAt
  have h1 : MeasurableSet (O.domRestrict (q ∘ (A.chart j).symm) ⁻¹' B) :=
    hc.domRestrict.measurable hB
  have h2 := hOo.measurableSet.subtype_image h1
  rwa [Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe] at h2
end GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
