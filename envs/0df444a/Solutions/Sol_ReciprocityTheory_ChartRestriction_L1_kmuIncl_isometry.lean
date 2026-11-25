-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.kmuIncl_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:49:25.851115+00:00
-- url     : https://prove2.me/submissions/028e1a3f-7cea-4a9f-8346-df56fab1a8f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ExistsExtendEndomorphismFractions
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KmuInclDenseRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_kmuIncl_norm

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
theorem _root_.solution : Isometry (kmuIncl l) :=
  AddMonoidHomClass.isometry_of_norm (kmuIncl l) (fun x => kmuIncl_norm l x)
end ReciprocityTheory.ChartRestriction.L1
