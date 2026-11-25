-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.tay_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:18.773881+00:00
-- url     : https://prove2.me/submissions/fbc51ffa-72da-4a43-8b89-022f9e24d3c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_local

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
theorem _root_.solution {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[𝓝 0] h) (s : Multiset (Fin g → ℂ)) : tay f s = tay h s := by
  ext n
  show mD f 0 (dirs n + s) / fct n = mD h 0 (dirs n + s) / fct n
  rw [mD_local hfh]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
