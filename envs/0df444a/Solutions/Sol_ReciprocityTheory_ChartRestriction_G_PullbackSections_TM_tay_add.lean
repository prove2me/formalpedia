-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.tay_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:25.149015+00:00
-- url     : https://prove2.me/submissions/7a14fc61-45d8-4bf2-82ab-75b49799423a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_add

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
theorem _root_.solution {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0)
    (s : Multiset (Fin g → ℂ)) : tay (f + h) s = tay f s + tay h s := by
  ext n
  rw [map_add]
  show mD (f + h) 0 (dirs n + s) / fct n = mD f 0 (dirs n + s) / fct n + mD h 0 (dirs n + s) / fct n
  rw [mD_add hf hh, add_div]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
