-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_AdditivityInDivisor_withBot_lt_of_add_one_le_ca3eb079d909
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:38:08.940942+00:00
-- url     : https://prove2.me/submissions/a22bca85-832b-4340-b3ba-e288707eec11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_WithBotLtOfAddOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
theorem _root_.solution {x : WithBot ℕ∞} {n : ℕ} (hx : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e] at hx
      exact absurd (WithBot.coe_le_coe.mp hx) (by simp)
    | coe m =>
      have h1 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by simpa using hx
      have h2 : m + 1 ≤ n := by exact_mod_cast h1
      have h3 : ((m : ℕ) : WithBot ℕ∞) < ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast (show m < n by omega)
      simpa using h3
end GroundTheory.Heights₂.Heights.NumbersDVR.AdditivityInDivisor
