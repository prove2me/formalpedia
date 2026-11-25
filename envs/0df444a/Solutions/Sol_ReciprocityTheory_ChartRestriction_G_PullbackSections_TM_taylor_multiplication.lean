-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.taylor_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:52.136415+00:00
-- url     : https://prove2.me/submissions/d1eea3ca-fc75-4858-9b9c-4b3e7918fc87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_local
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_tay_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_mul_coeff_low_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
theorem _root_.solution : TaylorMulSt := by
  refine ⟨fun g f h hf hh => ⟨?_, tay_add hf hh 0⟩, fun g c => tay_const c,
    fun g f h hfh => tay_local hfh 0⟩
  ext n
  exact taylor_mul_coeff_low_degree (n.degree + 1) f h hf hh n (Nat.lt_succ_self _)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
