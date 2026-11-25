-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.Closed.torusCoeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:59.554015+00:00
-- url     : https://prove2.me/submissions/c555db86-451a-4e41-b9b6-9e9537644d8c

import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCore
import Definitions.Def_ReciprocityTheory_SemistableReduction_SjHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
import Definitions.Def_ReciprocityTheory_SemistableReduction_HeightLowerBound
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCores
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMean
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLex
import Definitions.Def_ReciprocityTheory_SemistableReduction_GramOfLinearOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorus
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_torusMean_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed
open ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.MultiplicativeHeights.Closed
theorem _root_.solution : TorusCoeffStatement := torusMean_holds.2
end ReciprocityTheory.MultiplicativeHeights.Closed
