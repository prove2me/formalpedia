-- Prove2me | solution 1 for PI.FglPhSplit.Wk.orthogonalSplitPolarizationVanishes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:52:33.490701+00:00
-- url     : https://prove2.me/submissions/ed10f95d-96c9-4f14-95da-25fc4f53a8da

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_OrthogonalSplitPolarizationVanishes
import Theorems.Thm_PI_FglPhSplit_Wk_compositionalInverseSymm
import Theorems.Thm_PI_FglPhSplit_Wk_be_mulBy_zero

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
theorem _root_.solution : S2 := by
  intro K _ g hex hinv0 hph κ ι ι' _ _ _ a a' ha
  obtain ⟨hl0, hinv⟩ := compositionalInverseSymm K g.l g.ex hex hinv0
  simp only [Dat.sdR]
  refine Finset.sum_eq_zero fun f _ => Finset.sum_eq_zero fun f' _ => ?_
  simp only [ha f f', Prod.fst_zero]
  exact be_mulBy_zero g hex hph hl0 hinv _ (by simp)
end PI.FglPhSplit.Wk
