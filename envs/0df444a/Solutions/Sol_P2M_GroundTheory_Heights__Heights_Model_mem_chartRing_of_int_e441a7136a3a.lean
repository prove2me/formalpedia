-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_mem_chartRing_of_int_e441a7136a3a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:37.557608+00:00
-- url     : https://prove2.me/submissions/a63f6480-0a2f-4124-9087-b2284fbd9aeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37

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
theorem _root_.solution (R : Type*) [CommRing R] [Algebra R Ω] {y : Ω}
    (hy : y ∈ chartRing ℤ x i) : y ∈ chartRing R x i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact Algebra.subset_adjoin hy
  | algebraMap z => simp [intCast_mem_chartRing x i R z]
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz
end GroundTheory.Heights₂.Heights.Model
