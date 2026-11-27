-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.Closed.lemmaH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:15.386125+00:00
-- url     : https://prove2.me/submissions/07b0a0b8-7e17-4831-b8c4-6cdf896d761b

import Definitions.Def_ReciprocityTheory_SemistableReduction_LemmaH
import Definitions.Def_ReciprocityTheory_SemistableReduction_BalancedSchwarz
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanish
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxGraph
import Definitions.Def_ReciprocityTheory_SemistableReduction_ApproxBasis
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_DegAddHolds
import Definitions.Def_ReciprocityTheory_SemistableReduction_OnePolyGrowth
import Definitions.Def_ReciprocityTheory_SemistableReduction_BWPoly
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_MvBlowup
import Definitions.Def_ReciprocityTheory_SemistableReduction_LatAll
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_lemmaH_holds


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
theorem _root_.solution : LemmaHStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.lemmaH_holds
end ReciprocityTheory.MultiplicativeHeights.Closed
