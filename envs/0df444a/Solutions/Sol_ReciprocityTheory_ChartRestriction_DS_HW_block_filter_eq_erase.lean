-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.block_filter_eq_erase
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:34.359923+00:00
-- url     : https://prove2.me/submissions/742748c7-dbf3-4846-9f92-daf448d46009

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PieriRules_BlockSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open Polynomial Finset
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (β : Bool) {s : Fin n} (hs : ε s = β) :
    univ.filter (fun b => b ≠ s ∧ ε b = ε s) = (univ.filter (fun b => ε b = β)).erase s := by
  ext b
  simp [hs]
end ReciprocityTheory.ChartRestriction.DS.HW
