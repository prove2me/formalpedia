-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eeVd_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:24.68215+00:00
-- url     : https://prove2.me/submissions/d40c40e4-ced9-46d0-a7cd-6df485392d94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (r : Fin n) :
    eeVd E f r = -∑ s, E r s (f s) := by
  simp [eeVd, coordV, LinearMap.pi_apply, LinearMap.sum_apply]
end ReciprocityTheory.ChartRestriction.DS
