-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_cminor_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:50.587652+00:00
-- url     : https://prove2.me/submissions/992dee13-f20a-4601-858f-70dfbe14dbff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero

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
theorem _root_.solution {N : ℕ} [NeZero N] (E : Fin N → Fin N → Module.End ℂ M) {s t q s' t' q' : ℕ}
    (hq : q = q') (hs : s = s') (ht : t = t') (y : ℂ) :
    cminor E (whB_seg N s q) (whB_seg N t q) y = cminor E (whB_seg N s' q') (whB_seg N t' q') y := by
  subst hq hs ht; rfl
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
