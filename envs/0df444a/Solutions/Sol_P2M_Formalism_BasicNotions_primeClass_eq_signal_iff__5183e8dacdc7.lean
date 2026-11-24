-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_primeClass_eq_signal_iff__5183e8dacdc7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:31:14.705366+00:00
-- url     : https://prove2.me/submissions/fd417492-1ae2-42a7-a70e-1d8bc5cddcf3

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramified_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramQ_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_ramD_iff
import Theorems.Thm_Formalism_BasicNotions_primeClass_eq_signal_iff
import Theorems.Thm_Formalism_BasicNotions_dvd_condN_iff_primeClass
import Theorems.Thm_Formalism_BasicNotions_jacobi_d_eq_one_or
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


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
theorem _root_.solution (hp : p.Prime) : primeClass H p = .signal ↔
    ¬ p ∣ H.condN ∧ jacobiSym (-(H.d : ℤ)) p = -1 ∧ H.psAt p = 1 := by
  rw [primeClass_eq_signal_iff, not_dvd_condN_iff' hp]
  have key : p ≠ H.d → (jacobiSym (-(H.d : ℤ)) p ≠ 1 ↔ jacobiSym (-(H.d : ℤ)) p = -1) := fun hd => by
    rcases jacobi_d_eq_one_or hp hd with h | h <;> simp [h]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨h1, h2, h3⟩, (key h3).1 h4, h5⟩
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5⟩
    exact ⟨h1, h2, h3, (key h3).2 h4, h5⟩
end Formalism.BasicNotions
