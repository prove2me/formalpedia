-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.nsq_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:23:27.03642+00:00
-- url     : https://prove2.me/submissions/f07c58e4-5a8e-4e23-9a92-8e26cf229d0d

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
theorem _root_.solution (μ x y : Fin n → ℝ) : nsq (μ + x - y) - nsq (x - y) = nsq μ + 2 * dot μ (x - y) := by
  simp only [nsq, dot, Pi.add_apply, Pi.sub_apply, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl (fun _ _ => by ring)
end ReciprocityTheory.ChartRestriction.DS
