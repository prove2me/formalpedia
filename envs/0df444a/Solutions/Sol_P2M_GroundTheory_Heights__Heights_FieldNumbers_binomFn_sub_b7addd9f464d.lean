-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_binomFn_sub_b7addd9f464d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:45.807521+00:00
-- url     : https://prove2.me/submissions/8d9148a7-7336-45ab-a236-bc4ed6d7d0b5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (N : ℕ) (t : ℤ) :
    binomFn (N + 1) t - binomFn (N + 1) (t - 1) = binomFn N t := by
  unfold binomFn
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp
  · simp
  · obtain ⟨u, rfl⟩ : ∃ u : ℕ, t = u + 1 := ⟨(t - 1).toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
    have h1 : ((u : ℤ) + 1).toNat = u + 1 := by omega
    have h2 : ((u : ℤ) + 1 - 1).toNat = u := by omega
    have h3 := Nat.choose_succ_succ (u + N + 1) N
    rw [h1, h2, show u + 1 + (N + 1) = u + N + 1 + 1 by omega, h3,
      show u + (N + 1) = u + N + 1 by omega, show u + 1 + N = u + N + 1 by omega]
    push_cast
    ring
end GroundTheory.Heights₂.Heights.FieldNumbers
