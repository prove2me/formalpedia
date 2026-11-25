-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_primeClass_eq_splitK_iff__e0d20d268f0e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:26.748909+00:00
-- url     : https://prove2.me/submissions/60a3b68e-686c-4e87-9442-82dcff216d57

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramified_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramQ_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramD_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_splitK_iff
import Theorems.Thm_Formalism_BasicNotions_dvd_condN_iff_primeClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Formalism.FrobeniusOrbits Formalism.HC
namespace Formalism.BasicNotions
section cls
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}
private theorem not_dvd_condN_iff' (hp : p.Prime) :
    ¬ p ∣ H.condN ↔ p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d := by
  rw [dvd_condN_iff_primeClass H hp, primeClass_eq_ramified_iff, primeClass_eq_ramQ_iff,
    primeClass_eq_ramD_iff]
  tauto
end cls
namespace Ranks
variable (R : Ranks)
end Ranks
namespace Host
variable {R : Ranks} (H : Host R)
end Host
end Formalism.BasicNotions
end

set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
variable {φ : Frame} (H : HostRaw φ) {p : ℕ}
variable {H}
namespace Formalism.BasicNotions
theorem _root_.solution (hp : p.Prime) : primeClass H p = .splitK ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = 1 := by
  rw [primeClass_eq_splitK_iff, not_dvd_condN_iff' hp]
  tauto
end Formalism.BasicNotions
