-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.splitE_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:48.550932+00:00
-- url     : https://prove2.me/submissions/54014ea8-64a9-4f4a-a637-ed8f04b2ba42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution (p m : ℕ) : MeasurePreserving (splitE p m) volume volume := by
  have e1 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prodCongr
        (MeasurableEquiv.refl ((Fin m → ℂ) × ℝ)))) volume volume :=
    (MeasurePreserving.id volume).prod
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).prod (MeasurePreserving.id volume))
  have e2 : MeasurePreserving ((MeasurableEquiv.refl (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.prodAssoc :
        (ℂ × (Fin p → ℂ)) × ((Fin m → ℂ) × ℝ) ≃ᵐ ℂ × (Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    (MeasurePreserving.id volume).prod volume_preserving_prodAssoc
  have e3 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((Fin (p + 1) → ℂ) × ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        (Fin (p + 1) → ℂ) × ℂ × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))).symm volume volume :=
    MeasurePreserving.symm _ volume_preserving_prodAssoc
  have e4 : MeasurePreserving ((MeasurableEquiv.prodComm :
      (Fin (p + 1) → ℂ) × ℂ ≃ᵐ ℂ × (Fin (p + 1) → ℂ)).prodCongr
      (MeasurableEquiv.refl ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)))) volume volume :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id volume)
  have e5 : MeasurePreserving (MeasurableEquiv.prodAssoc :
      (ℂ × (Fin (p + 1) → ℂ)) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ)) ≃ᵐ
        ℂ × (Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) volume volume :=
    volume_preserving_prodAssoc
  have e6 : MeasurePreserving (MeasurableEquiv.prodComm :
      ℂ × ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) ≃ᵐ
        ((Fin (p + 1) → ℂ) × ((Fin p → ℂ) × ((Fin m → ℂ) × ℝ))) × ℂ) volume volume :=
    Measure.measurePreserving_swap
  exact e6.comp (e5.comp (e4.comp (e3.comp (e2.comp e1))))
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
