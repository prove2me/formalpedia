-- Prove2me | solution 1 for P2M_RH_Formalism_HC_HostRaw_ordCompl_q_2735571a88a0a567
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:30.482318+00:00
-- url     : https://prove2.me/submissions/88c1e53c-d4d2-414e-8388-440c8b389b9e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_HC_D7_ordCompl_eq
import Theorems.Thm_Formalism_HC_HostRaw_coprime_QSd_q


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : ordCompl[H.q] H.condN = H.QS * H.d := by
  rw [show H.condN = H.q ^ 1 * (H.QS * H.d) by ring]
  exact D7.ordCompl_eq H.q_prime _ ((Nat.Prime.coprime_iff_not_dvd H.q_prime).mp H.coprime_QSd_q.symm)
end Formalism.HC.HostRaw
