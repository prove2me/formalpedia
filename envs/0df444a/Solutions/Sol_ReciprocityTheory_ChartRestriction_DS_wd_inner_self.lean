-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.wd_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:24.281815+00:00
-- url     : https://prove2.me/submissions/2a3bf495-98fd-4e56-b31c-e5d965f7b158

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (x : M) : inner ℂ x x = ((‖x‖ : ℝ) : ℂ) ^ 2 :=
  inner_self_eq_norm_sq_to_K x
end ReciprocityTheory.ChartRestriction.DS
