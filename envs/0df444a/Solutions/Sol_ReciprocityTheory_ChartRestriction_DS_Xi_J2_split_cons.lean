-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.split_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:18.59872+00:00
-- url     : https://prove2.me/submissions/3e972527-4556-46a9-bb18-f0361c2e8e80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cons_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p : ℕ} {R : Type*} [MeasureSpace R] [SFinite (volume : Measure R)]
    (G : (Fin (p + 1) → ℂ) × R → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z, G z = ∫⁻ w : ℂ, ∫⁻ q : (Fin p → ℂ) × R, G (Fin.cons w q.1, q.2) := by
  have hpi := (MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => (volume : Measure ℂ)) 0).symm
  have hF : Measurable fun x : Fin (p + 1) → ℂ => ∫⁻ r : R, G (x, r) := hG.lintegral_prod_right'
  have hcons : ∀ w : ℂ, Measurable (fun q : (Fin p → ℂ) × R => ((Fin.cons w q.1 : Fin (p + 1) → ℂ), q.2)) := by
    intro w
    have hm : Measurable (fun q : (Fin p → ℂ) × R =>
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm (w, q.1), q.2)) := by
      first
      | exact ((MeasurableEquiv.measurable _).comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd
      | exact ((MeasurableEquiv.measurable _).comp (measurable_const.prod_mk measurable_fst)).prod_mk measurable_snd
    simpa only [cons_symm] using hm
  calc ∫⁻ z, G z = ∫⁻ x : Fin (p + 1) → ℂ, ∫⁻ r : R, G (x, r) := MeasureTheory.lintegral_prod _ hG.aemeasurable
    _ = ∫⁻ y : ℂ × (Fin p → ℂ), (∫⁻ r : R, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm y, r))
          ∂((volume : Measure ℂ).prod (volume : Measure (Fin p → ℂ))) := (hpi.lintegral_comp hF).symm
    _ = ∫⁻ w : ℂ, ∫⁻ q : Fin p → ℂ, ∫⁻ r : R, G (Fin.cons w q, r) := by
          rw [MeasureTheory.lintegral_prod (fun y : ℂ × (Fin p → ℂ) =>
            ∫⁻ r : R, G ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm y, r))
            (hF.comp (MeasurableEquiv.measurable _)).aemeasurable]
          simp only [cons_symm]
    _ = ∫⁻ w : ℂ, ∫⁻ q : (Fin p → ℂ) × R, G (Fin.cons w q.1, q.2) := by
          refine MeasureTheory.lintegral_congr fun w => ?_
          exact (MeasureTheory.lintegral_prod (fun q : (Fin p → ℂ) × R => G (Fin.cons w q.1, q.2))
            (hG.comp (hcons w)).aemeasurable).symm
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
