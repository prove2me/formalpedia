-- Prove2me | solution 1 for PI.SqPairLocal.isMaximal_comap_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:06.372831+00:00
-- url     : https://prove2.me/submissions/effa94ca-fc8e-4d9b-9e3d-a653d5af12ce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Theorems.Thm_PI_SqPairLocal_cj_surj

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
theorem _root_.solution {Q : Ideal (𝓞 E)} (hQ : Q.IsMaximal) : (Q.comap (cj E)).IsMaximal := by
  haveI := hQ
  exact Ideal.comap_isMaximal_of_surjective (cj E) cj_surj
end PI.SqPairLocal
