-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbAddBlock_comb_decomp_d0a17f4bc2c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:53:01.207799+00:00
-- url     : https://prove2.me/submissions/77e1140d-52d5-4eab-90fb-03bb61a3eccf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbAddBlock
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
variable {K : Type} [DecidableEq K] {ι : K → Type} {N : ℕ}
variable {F : Type u} [Field F]
omit [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
theorem _root_.solution (μ : (Σ o, addBlock ι N o) →₀ ℕ) :
    comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) = μ := by
  have h1 : ∀ j : Fin (N + 1), comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) (newVar ι N j) = μ (newVar ι N j) := by
    intro j
    have hn : newVar ι N j ∉ Set.range (addBlockIncl ι N) := by
      rintro ⟨v, hv⟩
      simpa [addBlockIncl, newVar] using congrArg Sigma.fst hv
    rw [comb, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hn,
      Finsupp.mapDomain_apply newVar_injective, Finsupp.comapDomain_apply, zero_add]
  have h2 : ∀ v : (Σ k, ι k), comb (μ.comapDomain (addBlockIncl ι N) addBlockIncl_injective.injOn)
      (μ.comapDomain (newVar ι N) newVar_injective.injOn) (addBlockIncl ι N v) =
        μ (addBlockIncl ι N v) := by
    intro v
    have hn : addBlockIncl ι N v ∉ Set.range (newVar ι N) := by
      rintro ⟨j, hj⟩
      simpa [addBlockIncl, newVar] using congrArg Sigma.fst hj
    rw [comb, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range _ _ hn,
      Finsupp.mapDomain_apply addBlockIncl_injective, Finsupp.comapDomain_apply, add_zero]
  ext ⟨_ | k, i⟩
  · exact h1 i
  · exact h2 ⟨k, i⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.HilbAddBlock
