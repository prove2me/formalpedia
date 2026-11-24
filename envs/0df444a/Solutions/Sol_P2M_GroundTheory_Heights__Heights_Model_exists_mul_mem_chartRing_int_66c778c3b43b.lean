-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_exists_mul_mem_chartRing_int_66c778c3b43b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:36.758444+00:00
-- url     : https://prove2.me/submissions/99af6350-723f-4562-811f-64630013af62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_ChartGlueLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_intCast_mem_chartRing_8f356cccfc37
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
theorem _root_.solution {y : Ω} (hy : y ∈ chartRing R x i) :
    ∃ t ∈ T, (t : Ω) * y ∈ chartRing ℤ x i := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_mem T, by rw [Int.cast_one, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective T r
    refine ⟨s, s.2, ?_⟩
    have h := congrArg (algebraMap R Ω) (IsLocalization.mk'_spec R a s)
    rw [map_mul, algebraMap_algebraMap_int, algebraMap_algebraMap_int] at h
    rw [mul_comm, h]
    exact intCast_mem_chartRing x i ℤ a
  | add y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨t', ht', htz⟩ := hz
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : ((t * t' : ℤ) : Ω) * (y + z) = (t' : Ω) * ((t : Ω) * y) + (t : Ω) * ((t' : Ω) * z) := by
      push_cast; ring
    rw [this]
    exact add_mem (mul_mem (intCast_mem_chartRing x i ℤ _) hty)
      (mul_mem (intCast_mem_chartRing x i ℤ _) htz)
  | mul y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨t', ht', htz⟩ := hz
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : ((t * t' : ℤ) : Ω) * (y * z) = ((t : Ω) * y) * ((t' : Ω) * z) := by
      push_cast; ring
    rw [this]
    exact mul_mem hty htz
end GroundTheory.Heights₂.Heights.Model
