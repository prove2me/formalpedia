-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.Closed.sj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:51.278717+00:00
-- url     : https://prove2.me/submissions/83f05be5-7569-4d2d-9a0f-a796b0a05626

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
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphereLinLog
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sj_holds


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
theorem _root_.solution : SJStatement := sj_holds sphereLinLog
end ReciprocityTheory.MultiplicativeHeights.Closed
