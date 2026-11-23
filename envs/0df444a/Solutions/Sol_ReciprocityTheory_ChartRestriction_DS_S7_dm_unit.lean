-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:26.090243+00:00
-- url     : https://prove2.me/submissions/89125e0a-6550-4760-9607-99e6ef80eb60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_UUh

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
theorem _root_.solution {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    ∑ j, U a j * star (U b j) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  have h := congrFun (congrFun (dm_UUh hU) a) b
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.conjTranspose_apply] using h
end ReciprocityTheory.ChartRestriction.DS.S7
