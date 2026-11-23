-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.bco_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:34.150865+00:00
-- url     : https://prove2.me/submissions/17f3601f-98df-46e6-b7d5-7e6186597646

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
theorem _root_.solution {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) :
    bco x l = (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I - bS x l := rfl
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
