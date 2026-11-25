-- Prove2me | solution 1 for UpperTheory.Small.factorization_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:14:19.185288+00:00
-- url     : https://prove2.me/submissions/9f3a3956-4862-472a-90c2-7a9b79ca0929

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
theorem _root_.solution {l : ℕ} (h : l ∉ H.small) : H.QS.factorization l = 0 := by
  rw [Nat.factorization_eq_zero_iff]
  by_contra hc
  push_neg at hc
  apply h
  simp only [Formalism.HC.HostRaw.small, Nat.mem_primeFactors]
  exact ⟨hc.1, hc.2.1, hc.2.2⟩
end UpperTheory.Small
