-- Prove2me | solution 1 for UpperTheory.Small.not_mem_of_dvd_qd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:22.07418+00:00
-- url     : https://prove2.me/submissions/22914ad4-50e0-4006-9b43-33cf7b1e1353

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
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
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
namespace UpperTheory.Small
theorem _root_.solution {l : ℕ} (hl : l ∣ H.q * H.d) : l ∉ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  rintro ⟨hp, hdq, -⟩
  have h1 : l ∣ Nat.gcd H.QS (H.q * H.d) := Nat.dvd_gcd hdq hl
  rw [H.QS_coprime.gcd_eq_one] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
end UpperTheory.Small
