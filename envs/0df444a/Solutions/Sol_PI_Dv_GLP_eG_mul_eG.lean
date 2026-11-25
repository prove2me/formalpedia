-- Prove2me | solution 1 for PI.Dv.GLP.eG_mul_eG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:33.169782+00:00
-- url     : https://prove2.me/submissions/da4b3b8c-6064-4d09-86dd-9000341246f2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw
import Theorems.Thm_PI_Dv_GLP_eS_mul_eS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Representation
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.GLP
theorem _root_.solution [CharZero K] (T : GoodSet K G) : eG T * eG T = eG T := by
  rw [eG, Finset.sum_mul_sum]
  simp_rw [eS_mul_eS]
  simp
end PI.Dv.GLP
