-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.lemmaN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:26:41.508522+00:00
-- url     : https://prove2.me/submissions/0cc91677-2d11-4f4e-9caf-be156ac275cd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_DimStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaN
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_thetaBasis_holds


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
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (_hd : DimStatement) : NStatement := thetaBasis_holds
end ReciprocityTheory.ChartRestriction.G.I2
