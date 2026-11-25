-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_coeff_killBlocks_263d92e57432
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:57.238868+00:00
-- url     : https://prove2.me/submissions/94140862-3c23-41c3-be3c-86bd4f3defaf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_monomial_ab5dd46129ab

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
theorem _root_.solution (T : Finset K) (q : MRing ι F) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (killBlocks T q) = if ∀ v ∈ d.support, v.1 ∉ T then coeff d q else 0 := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial d' c =>
    rw [killBlocks_monomial, apply_ite (coeff d), coeff_zero, coeff_monomial]
    by_cases hd : d' = d
    · subst hd
      simp
    · simp [hd]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
