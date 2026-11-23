-- Prove2me | solution 1 for P2M_RH_ReciprocityTheory_ChartRestriction_DS_nsq_root_da10e168d3dff856
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:29.11854+00:00
-- url     : https://prove2.me/submissions/29218768-4b1a-43d0-9df5-5c2624862f04

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
theorem _root_.solution {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by
  simp [nsq, dot, root, Pi.single_apply, mul_sub, sum_sub_distrib, hab, Ne.symm hab]
  norm_num
end ReciprocityTheory.ChartRestriction.DS
