-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:31.425366+00:00
-- url     : https://prove2.me/submissions/e078caa0-9142-4008-afed-650bf05edc95

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {i : ℕ} (hi : i ≤ n) (a b : Fin i) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hi a) (Fin.castLE hi b) = (1 : Matrix (Fin i) (Fin i) ℂ) a b := by
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    exact fun e => h (Fin.castLE_injective hi e)
end ReciprocityTheory.ChartRestriction.DS.S7
