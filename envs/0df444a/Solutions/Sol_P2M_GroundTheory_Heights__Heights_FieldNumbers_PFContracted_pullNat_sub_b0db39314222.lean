-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_sub_b0db39314222
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:58.368952+00:00
-- url     : https://prove2.me/submissions/3dcc98d1-0ca1-4fed-9dc1-a49cfd4158e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_apply_1b2c9c48af61

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (b : K → ℤ) :
    (fun k' => (pullNat K K' j (fun κ => (b κ).toNat) k' : ℤ) -
      pullNat K K' j (fun κ => (-b κ).toNat) k') = pullDeg j b := by
  funext k'
  rw [pullNat_apply, pullNat_apply, pullDeg]
  by_cases h : ∃ κ, j κ = k'
  · obtain ⟨κ, rfl⟩ := h
    rw [j.injective.extend_apply, j.injective.extend_apply, j.injective.extend_apply]
    exact Int.toNat_sub_toNat_neg (b κ)
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h,
      Function.extend_apply' _ _ _ h]
    simp
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
