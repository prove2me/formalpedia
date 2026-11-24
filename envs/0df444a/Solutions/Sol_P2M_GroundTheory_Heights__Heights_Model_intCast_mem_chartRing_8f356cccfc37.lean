-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:47.522915+00:00
-- url     : https://prove2.me/submissions/ca8ea1c2-04d1-46c7-9c89-cf542b61bddc

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
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (R : Type*) [CommRing R] [Algebra R Ω] (z : ℤ) :
    (z : Ω) ∈ chartRing R x i :=
  intCast_mem _ z
end GroundTheory.Heights₂.Heights.Model
