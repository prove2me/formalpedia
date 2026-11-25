-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.absDet_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:13:40.790943+00:00
-- url     : https://prove2.me/submissions/25446b5c-cb17-4d78-8b51-6cde972ca650

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegD
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_absDet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : AbsDetStatement := by
  intro n A C hA hC h
  exact sdd_absDet A C hA hC h
end ReciprocityTheory.MultiplicativeHeights
