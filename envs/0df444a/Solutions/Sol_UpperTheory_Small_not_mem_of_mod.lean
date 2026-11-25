-- Prove2me | solution 1 for UpperTheory.Small.not_mem_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:58:35.966862+00:00
-- url     : https://prove2.me/submissions/d31a98f2-133a-4d72-aa89-b83bfc9e4a1f

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
theorem _root_.solution {l : ℕ} (h : l % (H.QS * H.q * H.d) = 1) : l ∉ H.small := by
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  rintro ⟨hp, hdq, -⟩
  have hm : l ∣ H.QS * H.q * H.d := dvd_trans hdq (by rw [mul_assoc]; exact dvd_mul_right _ _)
  have h1 : l ∣ l % (H.QS * H.q * H.d) := (Nat.dvd_mod_iff hm).2 dvd_rfl
  rw [h] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
end UpperTheory.Small
