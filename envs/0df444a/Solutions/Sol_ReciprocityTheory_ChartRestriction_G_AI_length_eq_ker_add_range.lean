-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_eq_ker_add_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:05.044273+00:00
-- url     : https://prove2.me/submissions/1ac3fa72-191d-4191-98dc-6228682d13ab

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {A : Type*} [Ring A] {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N) :
    length A M = length A (LinearMap.ker φ) + length A (LinearMap.range φ) := by
  exact Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    (Submodule.injective_subtype _) φ.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
end ReciprocityTheory.ChartRestriction.G.AI
