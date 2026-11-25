-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlaceCentredSum_finsum_fibre_114cbf332dc8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:26.707489+00:00
-- url     : https://prove2.me/submissions/56b7bade-09a3-4da8-91ad-586e90a7fe71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlaceCentredSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPlaceCentredSum

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
open NumberField IsDedekindDomain Ideal
open GroundTheory.Heights₂.Heights.PlaceCentredSum
variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]
namespace GroundTheory.Heights₂.Heights.PlaceCentredSum
theorem _root_.solution {α β : Type*} (π : α → β) [∀ b, Fintype {a // π a = b}] (n : α → ℕ) (N : ℕ)
    (g : β → ℝ) (hg : g.support.Finite) (hsum : ∀ b, ∑ a : {a // π a = b}, n a.1 = N) :
    ∑ᶠ a, (n a : ℝ) * g (π a) = N * ∑ᶠ b, g b := by
  classical
  have hfin : ∀ b, (π ⁻¹' {b}).Finite := fun b ↦
    Set.finite_coe_iff.mp (Finite.of_fintype {a // π a = b})
  have hA : (π ⁻¹' g.support).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact hg.biUnion fun b _ ↦ hfin b
  rw [finsum_eq_sum_of_support_subset _ (s := hA.toFinset) ?_,
    finsum_eq_sum_of_support_subset _ (s := hg.toFinset) (by simp), Finset.mul_sum]
  · rw [← Finset.sum_fiberwise_of_maps_to (s := hA.toFinset) (t := hg.toFinset) (g := π)
      (fun a ha ↦ by simpa using ha)]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [Finset.sum_subtype (p := fun a ↦ π a = b) _ (fun a ↦ by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact ⟨And.right, fun h ↦ ⟨by rw [h]; simpa using hb, h⟩⟩)]
    have : ∀ a : {a // π a = b}, (n a.1 : ℝ) * g (π a.1) = n a.1 * g b := fun a ↦ by rw [a.2]
    rw [Fintype.sum_congr _ _ this, ← Finset.sum_mul, ← Nat.cast_sum, hsum]
  · intro a ha
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Function.mem_support]
    exact right_ne_zero_of_mul ha
end GroundTheory.Heights₂.Heights.PlaceCentredSum
