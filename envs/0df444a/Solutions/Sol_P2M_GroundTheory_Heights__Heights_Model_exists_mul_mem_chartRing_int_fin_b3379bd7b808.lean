-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_fin_b3379bd7b808
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:00.799799+00:00
-- url     : https://prove2.me/submissions/dbe9974f-42b2-4610-b1b8-0604ca866c22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_66c778c3b43b

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
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {ι : Type*} [Fintype ι] (y : ι → Ω)
    (hy : ∀ l, y l ∈ chartRing R x i) :
    ∃ t ∈ T, ∀ l, (t : Ω) * y l ∈ chartRing ℤ x i := by
  classical
  choose t ht hty using fun l => exists_mul_mem_chartRing_int x i R T (hy l)
  refine ⟨∏ l, t l, prod_mem fun l _ => ht l, fun l => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ l), Int.cast_mul, mul_comm (t l : Ω),
    mul_assoc]
  exact mul_mem (intCast_mem_chartRing x i ℤ _) (hty l)
end GroundTheory.Heights₂.Heights.Model
