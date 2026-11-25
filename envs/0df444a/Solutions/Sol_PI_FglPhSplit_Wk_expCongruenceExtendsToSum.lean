-- Prove2me | solution 1 for PI.FglPhSplit.Wk.expCongruenceExtendsToSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:42.614527+00:00
-- url     : https://prove2.me/submissions/a9780060-4b04-4c31-a0e4-2aa2adb2984d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_AddPreservesExpCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Theorems.Thm_PI_FglPhSplit_Wk_rho_PhOn
import Theorems.Thm_PI_FglPhSplit_Wk_rho_beSum
import Theorems.Thm_PI_FglPhSplit_Wk_simeqW_rho
import Theorems.Thm_PI_FglPhSplit_Wk_compositionalInverseSymm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglPhSplit PI.FglPhSplit.Wk
open PI.FglPhSplit
variable {K : Type} [Field K]
namespace PI.FglPhSplit.Wk
theorem _root_.solution : S4 := by
  intro K _ _ W g hex0 hinv κ ι ι' _ _ _ b b' h
  have hl0 := (compositionalInverseSymm K g.l g.ex hex0 hinv).1
  have h1 := simeqW_rho (ι' := ι') h
  rw [rho_PhOn g hex0 hl0, rho_beSum g hex0 hl0] at h1
  exact h1
end PI.FglPhSplit.Wk
