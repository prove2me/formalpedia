-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.tay_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:39:38.513341+00:00
-- url     : https://prove2.me/submissions/75b78626-cc7f-4fc5-be8b-8b1f3ab4f148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_mD_const

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
theorem _root_.solution (c : ℂ) : tay (g := g) (fun _ => c) 0 = C c := by
  ext n
  rw [MvPowerSeries.coeff_C]
  show mD (fun _ => c) 0 (dirs n + 0) / fct n = _
  rw [add_zero, mD_const]
  by_cases hn : n = 0
  · subst hn
    simp [dirs, fct]
  · have hd : dirs n ≠ 0 := by
      intro h0
      apply hn
      have h1 : Finsupp.toMultiset n = 0 := by simpa [dirs] using h0
      simpa using congrArg Multiset.toFinsupp h1
    rw [if_neg hd, if_neg hn, zero_div]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
