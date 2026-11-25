-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isLocalization_of_mem_iff_9d8ee689c59d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:26:33.784142+00:00
-- url     : https://prove2.me/submissions/8b3d9381-a295-45b5-92f7-7135e52a4123

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocQuotCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {O F : Type*} [CommRing O] [Field F] (φ : O →+* F) (hφ : Function.Injective φ)
    (L : Subring F) [Algebra O L] (hL : ∀ x : O, ((algebraMap O L x : L) : F) = φ x) (m : Ideal O) [m.IsPrime]
    (h : ∀ y : F, y ∈ L ↔ ∃ x s : O, s ∉ m ∧ y * φ s = φ x) :
    IsLocalization.AtPrime L m where
  map_units := by
    rintro ⟨s, hs⟩
    have hs0 : φ s ≠ 0 := fun h0 => hs (by rw [(map_eq_zero_iff φ hφ).1 h0]; exact m.zero_mem)
    refine IsUnit.of_mul_eq_one ⟨(φ s)⁻¹, (h _).2 ⟨1, s, hs, by rw [map_one, inv_mul_cancel₀ hs0]⟩⟩ ?_
    apply Subtype.ext
    simp only [Subring.coe_mul, hL, Subring.coe_one]
    exact mul_inv_cancel₀ hs0
  surj z := by
    obtain ⟨x, s, hs, hxs⟩ := (h z).1 z.2
    exact ⟨⟨x, ⟨s, hs⟩⟩, Subtype.ext (by simp only [Subring.coe_mul, hL]; exact hxs)⟩
  exists_of_eq {x y} hxy := ⟨1, by
    have h1 := congrArg Subtype.val hxy
    rw [hL, hL] at h1
    rw [hφ h1]⟩
end GroundTheory.Heights₂.Heights.Inter
