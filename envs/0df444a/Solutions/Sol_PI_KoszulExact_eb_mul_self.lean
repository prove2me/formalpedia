-- Prove2me | solution 1 for PI.KoszulExact.eb_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:33.568704+00:00
-- url     : https://prove2.me/submissions/d9869b3c-68f6-4dc0-b560-66774c4f33f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_ContractPowSuccMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
variable {R : Type u} [CommRing R] {D : ℕ}
namespace PI.KoszulExact
theorem _root_.solution (i : Fin D) : eb R i * eb R i = 0 :=
  ExteriorAlgebra.ι_sq_zero _
end PI.KoszulExact
