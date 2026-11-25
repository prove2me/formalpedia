-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_ker_quot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:57.216808+00:00
-- url     : https://prove2.me/submissions/15c7fa81-efe7-4c58-9f5f-13ef6b35158f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) {x : A} (hx : x ∉ q.asIdeal) :
    length A (LinearMap.ker (LinearMap.lsmul A N x)) = 0 := by
  have hsub : Subsingleton (LinearMap.ker (LinearMap.lsmul A N x)) := by
    refine ⟨fun a b => ?_⟩
    suffices h : ∀ c : LinearMap.ker (LinearMap.lsmul A N x), c = 0 by rw [h a, h b]
    intro c
    obtain ⟨n, hn⟩ := c
    have hn' : x • n = 0 := hn
    apply Subtype.ext
    show n = 0
    have h1 : x • e n = 0 := by rw [← map_smul, hn', map_zero]
    have h2 : e n = 0 := by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (e n)
      rw [← ha] at h1 ⊢
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem] at h1
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact (q.isPrime.mem_or_mem h1).resolve_left hx
    exact e.injective (by rw [h2, map_zero])
  exact Module.length_eq_zero_iff.2 hsub
end ReciprocityTheory.ChartRestriction.G.AI
