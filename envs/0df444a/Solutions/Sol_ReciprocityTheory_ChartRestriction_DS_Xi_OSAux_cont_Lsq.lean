-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.cont_Lsq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:34.806024+00:00
-- url     : https://prove2.me/submissions/bbfa6a9f-2541-4c27-9d1e-f7e662016d67

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
theorem _root_.solution {p m : ℕ} (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold ReciprocityTheory.ChartRestriction.DS.Xi.Lsq
  exact continuous_const.add (continuous_finsetSum _ (fun j _ => by
    by_cases h : j.val < l.val <;> simp only [h, ↓reduceIte] <;> fun_prop))
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
