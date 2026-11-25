-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_proof_50f5ecdcc75d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:00:29.025117+00:00
-- url     : https://prove2.me/submissions/2e60d763-ad4f-4d44-ad85-2416e0c171bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameIntNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_eventualValue_comp_47b47bf9c10c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameIntNum_mixedDiff_comp_cdf665d4760a

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
open GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)
namespace GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
theorem _root_.solution (h : RenameHilbFn.Statement.{u}) : RenameIntNum.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P n bs
  have hH : hilbFn (P.comap (rename σ)) = fun m => hilbFn P (m ∘ E.symm) :=
    funext fun m => h F S K' κ ι' E σ hσ P m
  unfold intNum
  rw [hH, mixedDiff_comp E.symm bs (hilbFn P),
    eventualValue_comp E.symm (mixedDiff (fun i => bs i ∘ E.symm) (hilbFn P))]
end GroundTheory.Heights₂.Heights.FieldNumbers.RenameIntNum
