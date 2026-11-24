-- Prove2me | solution 1 for PI.SqPairLocal.comap_cj_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:57:59.902557+00:00
-- url     : https://prove2.me/submissions/5388b3a0-eabe-4215-a8bf-92e40442bb54

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_cj_cj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
namespace PI.SqPairLocal
theorem _root_.solution (I : Ideal (𝓞 E)) : (I.comap (cj E)).comap (cj E) = I := by
  ext x
  simp only [Ideal.mem_comap, cj_cj]
end PI.SqPairLocal
