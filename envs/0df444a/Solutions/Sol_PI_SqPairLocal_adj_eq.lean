-- Prove2me | solution 1 for PI.SqPairLocal.adj_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:35.264663+00:00
-- url     : https://prove2.me/submissions/e2c86ff1-a68e-410d-bd20-22f86efa78b9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps

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
variable {E : Type} [Field E] [NumberField E] [StarRing E]
variable {N : ℕ}
variable {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {c : 𝓞 E} {L : Submodule (𝓞 E) (Fin N → E)}
omit hQ
namespace PI.SqPairLocal
theorem _root_.solution (e : Matrix (Fin N) (Fin N) E) : eᴴ * e = -(e * e - e) + (e + eᴴ - 1) * e := by
  noncomm_ring
end PI.SqPairLocal
