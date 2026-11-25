-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_finsum_mul_finsum_comm_695f77cd28bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:26.082816+00:00
-- url     : https://prove2.me/submissions/ea7b2c32-3441-4240-91d8-2321d3daa569

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_DivisorIdealBotUniformiser
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleFiniteSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IdealCycleSupportFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {α β : Type*} (a : α → ℤ) (c : α → β → ℤ) (n : β → ℤ)
    (ha : (Function.support a).Finite) (hc : ∀ W, (Function.support (c W)).Finite) :
    ∑ᶠ W, a W * ∑ᶠ U, c W U * n U = ∑ᶠ U, (∑ᶠ W, a W * c W U) * n U := by
  classical
  set S := ha.toFinset
  set T := S.biUnion (fun W => (hc W).toFinset)
  have hcT : ∀ W ∈ S, Function.support (c W) ⊆ ↑T := by
    intro W hW U hU
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨W, hW, (hc W).mem_toFinset.mpr hU⟩
  have hin : ∀ U, ∑ᶠ W, a W * c W U = ∑ W ∈ S, a W * c W U := by
    intro U
    apply finsum_eq_sum_of_support_subset
    intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW
  simp_rw [hin]
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := T)]
  · rw [Finset.sum_congr rfl (g := fun W => a W * ∑ U ∈ T, c W U * n U)]
    · simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    · intro W hW
      congr 1
      apply finsum_eq_sum_of_support_subset
      intro U hU
      exact hcT W hW (left_ne_zero_of_mul hU)
  · intro U hU
    obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hU)
    exact hcT W hW (right_ne_zero_of_mul hne)
  · intro W hW
    rw [Finset.mem_coe, ha.mem_toFinset]
    exact left_ne_zero_of_mul hW
end GroundTheory.Heights₂.Heights.NumbersDVR
