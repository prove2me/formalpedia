-- Prove2me | solution 1 for PI.SqfRootsInj.W.claim_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:17.289366+00:00
-- url     : https://prove2.me/submissions/4ba98ba9-09f3-4e81-a9f5-eee723aa7935

import Definitions.Def_Formalism_PeriodIntegrals_SqfRootsInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_ClaimOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (h1 : Witness) (h2 : Count) : PI.SqfRootsInj.Claim := by
  intro g r _ hr hg T hT
  exact h2 g r hr hg T fun f hf => ⟨(hT f hf).1, h1 g r f (hT f hf)⟩
end PI.SqfRootsInj.W
