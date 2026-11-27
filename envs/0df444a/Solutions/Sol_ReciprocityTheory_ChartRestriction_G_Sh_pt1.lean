-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:22.351968+00:00
-- url     : https://prove2.me/submissions/effa08a1-9321-4446-be08-f31bbf69da4f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TypicalCurveStructureConstants
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_nsmul_coprime_bijective_curves


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution : CoprimeMultiplicationBijective := by
  intro C _ _ _ v p hp hvp d G n hn gb hgb
  exact nsmul_coprime_bijective_curves G hp hvp n hn gb hgb
end ReciprocityTheory.ChartRestriction.G.Sh
