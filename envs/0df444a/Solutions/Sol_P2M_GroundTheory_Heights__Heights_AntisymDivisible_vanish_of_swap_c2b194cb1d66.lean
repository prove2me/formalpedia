-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_vanish_of_swap_c2b194cb1d66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:23.556176+00:00
-- url     : https://prove2.me/submissions/95e3b44a-2a45-4810-8672-4810caf50029

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AntisymDivisible
variable {σ : Type*} [DecidableEq σ]
namespace GroundTheory.Heights₂.Heights.AntisymDivisible
theorem _root_.solution (u v : σ) (P : MvPolynomial σ ℝ) (h : rename (Equiv.swap u v) P = -P) :
    ∀ x : σ → ℝ, x u = x v → eval x P = 0 := by
  intro x hx
  have e : x ∘ ⇑(Equiv.swap u v) = x := by
    funext w
    simp only [Function.comp]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hx]
    · rw [h2, hx]
    · rfl
  have := congrArg (eval x) h
  rw [eval_rename, e, map_neg] at this
  linarith
end GroundTheory.Heights₂.Heights.AntisymDivisible
