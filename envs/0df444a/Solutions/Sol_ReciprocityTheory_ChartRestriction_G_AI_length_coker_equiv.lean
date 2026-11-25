-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_coker_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:21.814375+00:00
-- url     : https://prove2.me/submissions/d5b7f3ab-7f7e-4bc7-a7bb-236a67096cdc

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
theorem _root_.solution {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (e : N ≃ₗ[A] N') (x : A) :
    length A (N ⧸ LinearMap.range (LinearMap.lsmul A N x)) =
      length A (N' ⧸ LinearMap.range (LinearMap.lsmul A N' x)) := by
  refine (Submodule.Quotient.equiv _ _ e ?_).length_eq
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨e m, by simp⟩
  · rintro ⟨m, rfl⟩
    exact ⟨x • e.symm m, ⟨e.symm m, rfl⟩, by simp⟩
end ReciprocityTheory.ChartRestriction.G.AI
