-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.biadditive_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:56.22327+00:00
-- url     : https://prove2.me/submissions/154fc9b2-c542-4679-abc2-5ecc18269204

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_addition_linear_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_addition_linear_snd

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution : BiaddBilinSt := by
  intro k _ _ d f h1 h2 n hn
  by_cases h : (∑ i, n (0, i)) = 1
  · exact addition_linear_snd k d f h2 n fun h' => hn ⟨h, h'⟩
  · exact addition_linear_fst k d f h1 n h
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
