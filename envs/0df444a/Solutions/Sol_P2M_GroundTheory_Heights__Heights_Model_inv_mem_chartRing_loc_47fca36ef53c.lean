-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_inv_mem_chartRing_loc_47fca36ef53c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:43.006932+00:00
-- url     : https://prove2.me/submissions/8ef6baf7-f3b0-44a6-98b4-c9cfd9e251ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_algebraMap_algebraMap_int_528386c43939

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
theorem _root_.solution {t : ℤ} (ht : t ∈ T) :
    (t : Ω) ≠ 0 ∧ (t : Ω)⁻¹ ∈ chartRing R x i := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units R (⟨t, ht⟩ : T)
  have h1 : algebraMap R Ω (↑u⁻¹ : R) * (t : Ω) = 1 := by
    rw [← algebraMap_algebraMap_int R t]
    have : algebraMap ℤ R t = (u : R) := hu.symm
    rw [this, ← map_mul, Units.inv_mul, map_one]
  have ht0 : (t : Ω) ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  refine ⟨ht0, ?_⟩
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Subalgebra.algebraMap_mem _ _
end GroundTheory.Heights₂.Heights.Model
