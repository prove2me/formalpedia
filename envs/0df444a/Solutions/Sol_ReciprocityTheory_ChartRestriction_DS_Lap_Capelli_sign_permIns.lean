-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sign_permIns
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:44.87015+00:00
-- url     : https://prove2.me/submissions/894f9be2-eb32-406b-87d8-a4368d0d6375

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc

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
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign (permIns i τ) : ℤˣ) : ℤ) = (-1) ^ (i : ℕ) * ((Equiv.Perm.sign τ : ℤˣ) : ℤ) := by
  simp [permIns, Equiv.Perm.sign_mul]
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
