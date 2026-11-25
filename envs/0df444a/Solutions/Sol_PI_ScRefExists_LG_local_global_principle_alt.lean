-- Prove2me | solution 1 for PI.ScRefExists.LG.local_global_principle_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:29.226324+00:00
-- url     : https://prove2.me/submissions/8fad47bd-48e6-4c5c-ac8b-37ab318dc064

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_LocGlob
import Theorems.Thm_PI_ScRefExists_LG_locGlob_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.LG
namespace PI.ScRefExists.LG
theorem _root_.solution : PI.ScRefExists.Sk.LocGlob := by
  intro I t ht
  exact locGlob_gen t ht
end PI.ScRefExists.LG
