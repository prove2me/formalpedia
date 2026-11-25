-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_nsq_add__e834c2ab7af1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:57.105137+00:00
-- url     : https://prove2.me/submissions/60015806-8741-4394-92e3-ee7137921952

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
theorem _root_.solution (x y : Fin n → ℝ) : nsq (x + y) = nsq x + 2 * dot x y + nsq y := by
  simp only [nsq, dot, Pi.add_apply, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl (fun _ _ => by ring)
end ReciprocityTheory.ChartRestriction.DS
