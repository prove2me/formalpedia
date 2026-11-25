-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_of_isMultiHomog_d5143d61805c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:44.753883+00:00
-- url     : https://prove2.me/submissions/2a4012d6-031e-41e6-b7ea-34aec79a4971

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_coeff_killBlocks_263d92e57432
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_weight_apply_eq_zero_iff_311ff90258dd

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution (T : Finset K) {p : MRing ι F} {b : K → ℕ}
    (hp : IsMultiHomog p b) : killBlocks T p = if ∀ k ∈ T, b k = 0 then p else 0 := by
  ext d
  rw [coeff_killBlocks]
  by_cases hd : coeff d p = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    have key : (∀ v ∈ d.support, v.1 ∉ T) ↔ ∀ k ∈ T, b k = 0 := by
      constructor
      · intro h k hk
        rw [← hw, weight_apply_eq_zero_iff]
        intro v hv hvk
        exact h v hv (hvk ▸ hk)
      · intro h v hv hvT
        have := h v.1 hvT
        rw [← hw, weight_apply_eq_zero_iff] at this
        exact this v hv rfl
    by_cases hb : ∀ k ∈ T, b k = 0
    · rw [if_pos (key.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (key.mp h)), if_neg hb, coeff_zero]
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
