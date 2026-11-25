-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_pullNat_apply_1b2c9c48af61
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:23:50.452672+00:00
-- url     : https://prove2.me/submissions/3ef5a490-4da4-417b-8efb-d3895c567aab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted

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
theorem _root_.solution (e : K → ℕ) (k' : K') :
    (pullNat K K' j e k' : ℤ) = Function.extend j (fun κ => (e κ : ℤ)) 0 k' := by
  by_cases h : ∃ κ, j κ = k'
  · obtain ⟨κ, rfl⟩ := h
    rw [j.injective.extend_apply]
    simp [pullNat, Finset.sum_apply, Pi.single_apply, j.injective.eq_iff]
  · rw [Function.extend_apply' _ _ _ h]
    simp only [pullNat, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_zero]
    · simp
    · intro κ _
      rw [if_neg (fun hk => h ⟨κ, hk.symm⟩), mul_zero]
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
