-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_nsq_sub__a7aa378eee5a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:36.802775+00:00
-- url     : https://prove2.me/submissions/a8fbca3f-4438-4de7-8240-773b6aa26577

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
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (x y : Fin n → ℝ) : nsq (x - y) = nsq x - 2 * dot x y + nsq y := by
  simp only [nsq, dot, Pi.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl (fun _ _ => by ring)
end ReciprocityTheory.ChartRestriction.DS
