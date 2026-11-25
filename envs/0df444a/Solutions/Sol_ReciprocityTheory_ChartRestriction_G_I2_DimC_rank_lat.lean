-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.DimC.rank_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:36.557177+00:00
-- url     : https://prove2.me/submissions/fe50fc4a-f8be-4f60-a3f7-5665bd8fefe4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex Module
noncomputable section
open ReciprocityTheory.ChartRestriction.G.I2.DimC
variable {ι : Type} [Fintype ι]
variable (Y : GT ι)
namespace ReciprocityTheory.ChartRestriction.G.I2.DimC
theorem _root_.solution : finrank ℤ (lat Y.b) = 2 * Fintype.card ι := by
  rw [Module.finrank_eq_card_basis (Y.b.restrictScalars ℤ), Fintype.card_fin]
end ReciprocityTheory.ChartRestriction.G.I2.DimC
