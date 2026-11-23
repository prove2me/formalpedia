-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.eeV_coord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:55.515175+00:00
-- url     : https://prove2.me/submissions/8f0ad0b5-6239-4a6d-9423-6569d8da320e

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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (s : Fin n) :
    eeV E f s = ∑ r, E r s (f r) := by
  simp [eeV, coordV, LinearMap.pi_apply, LinearMap.sum_apply]
end ReciprocityTheory.ChartRestriction.DS
