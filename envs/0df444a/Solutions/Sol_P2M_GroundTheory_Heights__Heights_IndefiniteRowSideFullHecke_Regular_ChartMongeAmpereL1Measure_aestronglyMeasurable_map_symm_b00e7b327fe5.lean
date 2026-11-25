-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Regular_ChartMongeAmpereL1Measure_aestronglyMeasurable_map_symm_b00e7b327fe5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:06.799819+00:00
-- url     : https://prove2.me/submissions/a6e11b0b-5781-428d-acf2-3c24accf9953

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_ChartMongeAmpereL1Hypotheses
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_AestronglyMeasurableMapSymm
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_measurable_piecewise
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular
open MeasureTheory Filter Topology Set
open scoped ENNReal
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot maMeasure ChartPartition locDens)
open GroundTheory.Heights₂.Heights.Regular (PotentialCharts)
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
theorem _root_.solution {D : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (b : OpenPartialHomeomorph X (Fin D → ℂ)) {M : Set (Fin D → ℂ)}
    (hM : MeasurableSet M) (hMt : M ⊆ b.target) {g : X → ℝ}
    (hg : AEStronglyMeasurable (fun z => g (b.symm z)) (volume.restrict M)) :
    AEStronglyMeasurable g ((volume.restrict M).map b.symm) := by
  classical
  set ψ : X → (Fin D → ℂ) := b.source.piecewise b (fun _ => 0) with hψ
  have hψm : Measurable ψ :=
    b.continuousOn.measurable_piecewise continuousOn_const b.open_source.measurableSet
  set bad : Set (Fin D → ℂ) := {z | g (b.symm z) ≠ hg.mk _ z} with hbad
  have hbad0 : (volume.restrict M) bad = 0 := ae_iff.1 hg.ae_eq_mk
  set N := toMeasurable (volume.restrict M) bad with hN
  have hN0 : (volume.restrict M) N = 0 := by rw [hN, measure_toMeasurable]; exact hbad0
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  set S : Set X := ψ ⁻¹' (N ∪ Mᶜ) ∪ b.sourceᶜ with hS
  have hSm : MeasurableSet S :=
    (hψm (hNm.union hM.compl)).union b.open_source.measurableSet.compl
  have hsymm : AEMeasurable b.symm (volume.restrict M) :=
    (b.continuousOn_symm.mono hMt).aemeasurable hM
  refine ⟨fun x => hg.mk _ (ψ x), hg.stronglyMeasurable_mk.comp_measurable hψm, ?_⟩
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (t := S) ?_ ?_
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    by_contra hxS
    simp only [hS, mem_union, mem_preimage, mem_compl_iff, not_or, not_not] at hxS
    obtain ⟨⟨hxN, hxM⟩, hxs⟩ := hxS
    have hψx : ψ x = b x := by simp [hψ, hxs]
    rw [hψx] at hxN hxM hx
    have hxb : g (b.symm (b x)) = hg.mk _ (b x) := by
      by_contra h
      exact hxN (subset_toMeasurable _ _ h)
    rw [b.left_inv hxs] at hxb
    exact hx hxb
  · rw [Measure.map_apply_of_aemeasurable hsymm hSm, Measure.restrict_apply' hM]
    refine measure_mono_null (t := N ∩ M) ?_ ?_
    · rintro z ⟨hz, hzM⟩
      refine ⟨?_, hzM⟩
      have hzs : b.symm z ∈ b.source := b.map_target (hMt hzM)
      have hψz : ψ (b.symm z) = z := by simp [hψ, hzs, b.right_inv (hMt hzM)]
      simp only [hS, mem_preimage, mem_union, mem_compl_iff, hψz] at hz
      rcases hz with (hz | hz) | hz
      · exact hz
      · exact absurd hzM hz
      · exact absurd hzs hz
    · rwa [← Measure.restrict_apply hNm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartMongeAmpereL1Measure
