-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.locLen_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:06.224441+00:00
-- url     : https://prove2.me/submissions/a1953524-98ec-4304-a8d6-d08d7a74b187

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
variable {A : Type u} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {N₁ N₂ N₃ : Type v} [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂]
    [Module A N₂] [AddCommGroup N₃] [Module A N₃] (f : N₁ →ₗ[A] N₂) (g : N₂ →ₗ[A] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (p : PrimeSpectrum A) : locLen N₂ p = locLen N₁ p + locLen N₃ p := by
  unfold locLen
  refine Module.length_eq_add_of_exact (LocalizedModule.map p.asIdeal.primeCompl f)
    (LocalizedModule.map p.asIdeal.primeCompl g) ?_ ?_ ?_
  · first
      | exact LocalizedModule.map_injective _ _ hf
      | exact LocalizedModule.map_injective _ f hf
      | exact LocalizedModule.map_injective hf
  · first
      | exact LocalizedModule.map_surjective _ _ hg
      | exact LocalizedModule.map_surjective _ g hg
      | exact LocalizedModule.map_surjective hg
  · first
      | exact LocalizedModule.map_exact _ _ _ hex
      | exact LocalizedModule.map_exact _ f g hex
      | exact LocalizedModule.map_exact hex
end ReciprocityTheory.ChartRestriction.G.AI
