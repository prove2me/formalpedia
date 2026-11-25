-- Prove2me | solution 1 for PI.TwNormLat.W.combL_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:31:13.704486+00:00
-- url     : https://prove2.me/submissions/11caa9d5-9fb4-492c-b03e-285679dae9e3

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {K : Type} [Field K] {n : ℕ}
namespace PI.TwNormLat.W
theorem _root_.solution (b : Fin n → Fin n → K) (l : Fin n) : combL b (Pi.single l 1) = b l := by
  rw [combL_apply, Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => absurd (Finset.mem_univ l) h), Pi.single_eq_same, one_smul]
end PI.TwNormLat.W
