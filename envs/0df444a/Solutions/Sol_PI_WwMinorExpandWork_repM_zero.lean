-- Prove2me | solution 1 for PI.WwMinorExpandWork.repM_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:24:50.554044+00:00
-- url     : https://prove2.me/submissions/d10c3c6c-546f-4bc8-abb2-cfc0fdd71d36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMinorExpand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorExpansion_WwMinorExpandMain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.WwMinorExpandWork
open PI.WwMinorExpand
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)
namespace PI.WwMinorExpandWork
theorem _root_.solution (s : Lt) (p : ℕ) : RepM N0 N1 s p 0 :=
  ⟨0, by simp⟩
end PI.WwMinorExpandWork
