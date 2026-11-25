-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymDivisible_dvd_of_vanish_ea25bc3f8fad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:24.819445+00:00
-- url     : https://prove2.me/submissions/d85c2323-30f7-4c81-be7d-a52ecbcae3cb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymDivisible
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymDivisible_sub_rename_collapse_mem_70f922bc8132

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
theorem _root_.solution (u v : σ) (P : MvPolynomial σ ℝ)
    (h : ∀ x : σ → ℝ, x u = x v → eval x P = 0) : (X u - X v) ∣ P := by
  have h0 : rename (collapse u v) P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_rename, map_zero]
    apply h
    simp only [Function.comp, collapse, if_pos rfl]
    split_ifs <;> rfl
  have := sub_rename_collapse_mem u v P
  rw [h0, sub_zero] at this
  exact Ideal.mem_span_singleton.1 this
end GroundTheory.Heights₂.Heights.AntisymDivisible
