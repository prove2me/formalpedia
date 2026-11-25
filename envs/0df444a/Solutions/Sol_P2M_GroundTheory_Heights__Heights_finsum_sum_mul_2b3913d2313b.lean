-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_finsum_sum_mul_2b3913d2313b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:32:36.481751+00:00
-- url     : https://prove2.me/submissions/89998d0e-68b1-4739-9eff-1aa678683fb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardEmbeddingsRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {α ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → α → ℝ)
    (hg : ∀ k, (Function.support (g k)).Finite) :
    ∑ᶠ a, ∑ k, c k * g k a = ∑ k, c k * ∑ᶠ a, g k a := by
  have hS : (⋃ k, Function.support (g k)).Finite := Set.finite_iUnion hg
  have hsub : ∀ k, Function.support (g k) ⊆ hS.toFinset := fun k ↦ by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun k ↦ Function.support (g k)) k
  have hsum : Function.support (fun a ↦ ∑ k, c k * g k a) ⊆ hS.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset, Set.mem_iUnion]
    by_contra h
    push Not at h
    exact ha (Finset.sum_eq_zero fun k _ ↦ by rw [Function.notMem_support.mp (h k), mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hsum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [finsum_eq_sum_of_support_subset _ (hsub k), Finset.mul_sum]
end GroundTheory.Heights₂.Heights
