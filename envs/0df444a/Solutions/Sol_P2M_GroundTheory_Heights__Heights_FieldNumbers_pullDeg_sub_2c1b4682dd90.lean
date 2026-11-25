-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_sub_2c1b4682dd90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:41.576091+00:00
-- url     : https://prove2.me/submissions/41270ad3-e7c1-4a71-8e25-a3fb37286ba5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_self_4752179a6926
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_apply_not_5b15fa7008a2

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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
variable [DecidableEq K] [DecidableEq K']
variable {F : Type u} [Field F]
omit [DecidableEq K] [DecidableEq K']
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (bf bg : K → ℕ) :
    pullDeg j (fun k => (bf k : ℤ) - bg k) =
      fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ) := by
  funext k'
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    simp only [pullDeg, extend_apply_self]
  · simp only [pullDeg, extend_apply_not j _ k' h]
    simp
end GroundTheory.Heights₂.Heights.FieldNumbers
