-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_algebraMap_algebraMap_int_528386c43939
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:33.878459+00:00
-- url     : https://prove2.me/submissions/f2a82778-913c-42de-97c9-0c928197436e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open ReciprocityTheory.ChartRestriction.G.Geo
variable {Ω : Type*} [Field Ω] {τ : Type*} (x : τ → Ω) (i : τ)
variable (R : Type*) [CommRing R] [Algebra ℤ R] (T : Submonoid ℤ) [IsLocalization T R] [Algebra R Ω]
omit [IsLocalization T R]
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (z : ℤ) : algebraMap R Ω (algebraMap ℤ R z) = z := by
  rw [eq_intCast (algebraMap ℤ R), map_intCast]
end GroundTheory.Heights₂.Heights.Model
