-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:17:38.035569+00:00
-- url     : https://prove2.me/submissions/f16136cc-b86c-4cb2-8e82-f4d13a937bca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsPairs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimC_dim_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution : DimStatement :=
  fun _ _ Y q hq => DimC.dim_core Y q hq
end ReciprocityTheory.ChartRestriction.G.I2
