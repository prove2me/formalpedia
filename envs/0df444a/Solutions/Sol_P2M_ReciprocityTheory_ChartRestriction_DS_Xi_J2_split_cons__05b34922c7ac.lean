-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons__05b34922c7ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:57.130533+00:00
-- url     : https://prove2.me/submissions/28d3fb17-80e0-48ea-9eff-cca22d93b1c8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_cons_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_J2_split_cons

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
    ∫⁻ z, G z = ∫⁻ q : (Fin p → ℂ) × R, ∫⁻ w : ℂ, G (Fin.cons w q.1, q.2) := by
  rw [split_cons G hG]
  apply MeasureTheory.lintegral_lintegral_swap
  apply Measurable.aemeasurable
  have hm : Measurable (fun x : ℂ × ((Fin p → ℂ) × R) =>
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm (x.1, x.2.1), x.2.2)) := by
    first
    | exact ((MeasurableEquiv.measurable _).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)
    | exact ((MeasurableEquiv.measurable _).comp (measurable_fst.prod_mk (measurable_fst.comp measurable_snd))).prod_mk
        (measurable_snd.comp measurable_snd)
  have h2 := hG.comp hm
  simp only [cons_symm] at h2
  exact h2
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
