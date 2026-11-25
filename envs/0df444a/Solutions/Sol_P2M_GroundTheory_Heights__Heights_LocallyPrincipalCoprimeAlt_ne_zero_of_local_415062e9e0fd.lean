-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_ne_zero_of_local_415062e9e0fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:35.318882+00:00
-- url     : https://prove2.me/submissions/385d7e6b-2e04-4612-a7ca-62f68a7d03b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
theorem _root_.solution {B : Subring L} {M : AddSubgroup L} {ι : Type} {a : ι → L} {m : Ideal B} {i : ι}
    (hi : ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) (hM : M ≠ ⊥) : a i ≠ 0 := by
  obtain ⟨z, hzM, hz0⟩ : ∃ z ∈ M, z ≠ 0 := by
    by_contra h
    push Not at h
    exact hM ((AddSubgroup.eq_bot_iff_forall M).mpr h)
  obtain ⟨b, c, hbm, hbc⟩ := hi z hzM
  intro ha
  have hb : (b : L) ≠ 0 := fun h => hbm (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)
  rw [ha, mul_zero] at hbc
  exact mul_ne_zero hb hz0 hbc
end GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
