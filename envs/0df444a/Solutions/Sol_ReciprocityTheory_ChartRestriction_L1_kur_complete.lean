-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kur_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:04.470034+00:00
-- url     : https://prove2.me/submissions/5bd08a34-f9cf-470b-9c3f-cb1704118734

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_Statement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable (l : ℕ) [Fact l.Prime]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution : CompleteSpace (MaximalUnramifiedExtension l) :=
  (Subfield.isClosed_topologicalClosure (Kmu l)).completeSpace_coe
end ReciprocityTheory.ChartRestriction.L1
