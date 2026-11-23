-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.phi_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:02.892893+00:00
-- url     : https://prove2.me/submissions/caeee42c-af3d-4f9b-bc3a-d731e2f6563c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PositionPrependMemNoncompactPositionSubmodule
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_PhiPerm

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
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) (F : Big n k M) : phi E k F = ∑ κ, word E κ (F κ) := by
  simp only [phi, LinearMap.sum_apply, LinearMap.comp_apply]
  rfl
end ReciprocityTheory.ChartRestriction.DS
