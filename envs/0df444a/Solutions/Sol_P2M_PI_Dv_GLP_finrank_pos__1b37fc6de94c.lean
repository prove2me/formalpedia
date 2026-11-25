-- Prove2me | solution 1 for P2M_PI_Dv_GLP_finrank_pos__1b37fc6de94c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:17.659983+00:00
-- url     : https://prove2.me/submissions/04e02fe7-32f4-4305-a46e-428d33ee1b02

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_FinrankIntertw

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
theorem _root_.solution (T : GoodSet K G) (s : T.S) : (0 : ℕ) < Module.finrank K (T.W s) :=
  Module.finrank_pos
end PI.Dv.GLP
