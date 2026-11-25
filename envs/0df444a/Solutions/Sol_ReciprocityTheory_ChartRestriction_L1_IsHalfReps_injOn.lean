-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.IsHalfReps.injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:12:42.083469+00:00
-- url     : https://prove2.me/submissions/a6081299-6c0c-4450-a553-0fd87d34d2f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedHalf
import Theorems.Thm_Formalism_L2_Th1_F_pInjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}
namespace ReciprocityTheory.ChartRestriction.L1
namespace IsHalfReps
theorem _root_.solution (h : IsHalfReps L α T) : Set.InjOn L.weierstrassP (T : Set ℂ) := by
  intro P hP Q hQ hPQ
  exact h.2.1 P hP Q hQ ((pInjective L P Q (h.notMem hP) (h.notMem hQ)).mp hPQ)
end IsHalfReps
end ReciprocityTheory.ChartRestriction.L1
