-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.cons_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:07:34.514076+00:00
-- url     : https://prove2.me/submissions/c27ea769-68d8-441f-a718-f29e4ef87255

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero

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
theorem _root_.solution {p : ℕ} (q : ℂ × (Fin p → ℂ)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℂ) 0).symm q = Fin.cons q.1 q.2 := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  first
  | exact Fin.insertNth_zero' q.1 q.2
  | simp [Fin.insertNthEquiv, Fin.insertNth_zero']
  | rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
