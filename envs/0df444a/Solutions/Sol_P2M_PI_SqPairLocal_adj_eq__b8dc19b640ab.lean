-- Prove2me | solution 1 for P2M_PI_SqPairLocal_adj_eq__b8dc19b640ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:50:13.2691+00:00
-- url     : https://prove2.me/submissions/dbc782ab-5eaf-45fd-8f0c-9b5fe37fe25e

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
theorem _root_.solution (e : Matrix (Fin N) (Fin N) E) :
    (1 - e)ᴴ * (1 - e) = -(e * e - e) + -((e + eᴴ - 1) * (1 - e)) := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
  noncomm_ring
end PI.SqPairLocal
