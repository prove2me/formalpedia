-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_proof_3cd4b9fef857
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:26.840704+00:00
-- url     : https://prove2.me/submissions/5442166d-3aa7-43fe-a937-2656712a82d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagSwapDivisible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagSwapDivisible_dvd_sub_substitute_1e0e4f0fc4be

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagSwapDivisible
theorem _root_.solution : FlagSwapDivisible.Statement := by
  intro σ _ P a b hab hP
  set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg
  have hswap : g ∘ Equiv.swap a b = g := by
    funext v
    simp only [Function.comp_apply, hg]
    rcases eq_or_ne v a with rfl | hva
    · simp [Equiv.swap_apply_left, hab.symm]
    · rcases eq_or_ne v b with rfl | hvb
      · simp [Equiv.swap_apply_right, hva]
      · simp [Equiv.swap_apply_of_ne_of_ne hva hvb, hva]
  have hzero : aeval g P = 0 := by
    have h1 : aeval g P = -aeval g P := by
      calc aeval g P = aeval (g ∘ Equiv.swap a b) P := by rw [hswap]
        _ = aeval g (rename (Equiv.swap a b) P) := (aeval_rename _ _ _).symm
        _ = -aeval g P := by rw [hP, map_neg]
    have h2 : aeval g P + aeval g P = 0 := by
      nth_rewrite 2 [h1]; exact add_neg_cancel _
    have h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd := FlagSwapDivisible.dvd_sub_substitute a b P
  rw [← hg, hzero, sub_zero] at hd
  exact hd
end FlagSwapDivisible
end GroundTheory.Heights₂.Heights.RestTerms
