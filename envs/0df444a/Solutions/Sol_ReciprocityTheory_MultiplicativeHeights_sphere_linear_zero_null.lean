-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphere_linear_zero_null
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:50:30.300657+00:00
-- url     : https://prove2.me/submissions/69a060fe-ac79-4873-8b31-f444a8529673

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_inner_conjVec
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_norm_conjVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    (LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ
  have hK : K ≠ ⊤ := by
    intro h
    have hm : conjVec c ∈ K := h ▸ Submodule.mem_top
    have hm' : inner ℂ (conjVec c) (conjVec c) = 0 := hm
    rw [inner_self_eq_zero] at hm'
    exact hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])
  have hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} =
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, spherePoint, inner_conjVec]
  have hs : MeasurableSet
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [hset, Measure.toSphere_apply' _ hs,
    measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]
  rintro _ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩
  exact K.smul_mem t hz
end ReciprocityTheory.MultiplicativeHeights
