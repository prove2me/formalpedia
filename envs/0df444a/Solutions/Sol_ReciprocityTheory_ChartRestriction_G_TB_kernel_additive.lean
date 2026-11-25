-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.kernel_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:07.906257+00:00
-- url     : https://prove2.me/submissions/2cd763de-7061-49ba-ac50-adfe16c1221e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_killAdd_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_quadratic_column_derivative


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : KillAddSt := killAdd_of quadratic_column_derivative
end ReciprocityTheory.ChartRestriction.G.TB
