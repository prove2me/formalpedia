-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.J2.cont_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:23.881207+00:00
-- url     : https://prove2.me/submissions/43f1de12-24b2-42ff-a6fa-1216eb18684a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaugeSplittingAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.J2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.J2
theorem _root_.solution {p : ℕ} : Continuous fun q : ℂ × (Fin p → ℂ) => (Fin.cons q.1 q.2 : Fin (p + 1) → ℂ) := by
  refine continuous_pi fun j => ?_
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply i).comp continuous_snd
end ReciprocityTheory.ChartRestriction.DS.Xi.J2
