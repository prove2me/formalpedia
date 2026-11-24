-- Prove2me | solution 1 for PI.SqPairLocal.pres_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:35:10.298003+00:00
-- url     : https://prove2.me/submissions/e540fe0f-3e18-4421-9332-59d15585168c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj

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
variable {L : Submodule (𝓞 E) (Fin N → E)}
namespace PI.SqPairLocal
theorem _root_.solution {e f : Matrix (Fin N) (Fin N) E} (he : Pres L e) (hf : Pres L f) :
    Pres L (e - f) := by
  intro y hy
  rw [Matrix.sub_mulVec]
  exact L.sub_mem (he y hy) (hf y hy)
end PI.SqPairLocal
