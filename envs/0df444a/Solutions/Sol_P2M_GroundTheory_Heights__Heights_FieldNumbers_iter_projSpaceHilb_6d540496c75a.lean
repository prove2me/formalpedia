-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_6d540496c75a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:54:09.145502+00:00
-- url     : https://prove2.me/submissions/9be5881f-9459-4e27-882a-4835ecf4eab5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_apply_0b5964759951

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (N : ℕ) : ∀ j : ℕ, j ≤ N → ∀ s : ℕ,
    diff1^[j] (projSpaceHilb N) ((s : ℤ) + j) = (((s + N).choose (N - j) : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro _ s
    simp [projSpaceHilb]
  | succ j ih =>
    intro hj s
    have e1 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) = ((s + 1 : ℕ) : ℤ) + j := by push_cast; ring
    have e2 : (s : ℤ) + ((j + 1 : ℕ) : ℤ) - 1 = (s : ℤ) + j := by push_cast; ring
    rw [Function.iterate_succ_apply', backwardDifference_apply, e2, e1, ih (by omega), ih (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, N - j = k + 1 := ⟨N - (j + 1), by omega⟩
    have hk' : N - (j + 1) = k := by omega
    rw [hk, hk', show s + 1 + N = (s + N) + 1 by omega, Nat.choose_succ_succ']
    push_cast
    ring
end GroundTheory.Heights₂.Heights.FieldNumbers
