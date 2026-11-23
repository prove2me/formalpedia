-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_seg_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:09.89474+00:00
-- url     : https://prove2.me/submissions/8f96d1e6-b43b-40cc-9e37-7d9361e0bebd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_cast_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {N s q : ℕ} [NeZero N] (h : s + q ≤ N) (i : Fin q) :
    (whB_seg N s q i : ℕ) = s + i := by
  unfold whB_seg; exact whB_cast_val (by omega)
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
