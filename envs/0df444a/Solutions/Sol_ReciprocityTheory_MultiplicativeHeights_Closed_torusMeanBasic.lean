-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.Closed.torusMeanBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:51:48.567274+00:00
-- url     : https://prove2.me/submissions/90bd19ee-9aa7-4731-ad6a-fdc1128e3304

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
theorem _root_.solution : TorusMeanBasicStatement := torusMean_holds.1
end ReciprocityTheory.MultiplicativeHeights.Closed
