-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphereProb_inner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:06:04.570149+00:00
-- url     : https://prove2.me/submissions/8ab8f81e-dc13-4cfa-ab83-f840537d3704

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap

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
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} {u : EuclideanSpace ℂ (Fin n)} (hu : u ≠ 0) :
    sphereProb n {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0} = 0 := by
  set s : Set (UnitSphereC n) := {z | inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0}
  have hs : MeasurableSet s :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  let P : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ)
  have hP : P ≠ ⊤ := by
    intro h
    have hmem : u ∈ P := h ▸ Submodule.mem_top
    simp only [P, LinearMap.mem_ker, LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply] at hmem
    exact hu (inner_self_eq_zero.mp hmem)
  have hsub : Set.Ioo (0 : ℝ) 1 • ((↑) '' s : Set (EuclideanSpace ℂ (Fin n))) ⊆ (P : Set (EuclideanSpace ℂ (Fin n))) := by
    rintro _ ⟨r, -, y, ⟨z, hz, rfl⟩, rfl⟩
    show (((innerSL ℂ u : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ) :
      EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ).restrictScalars ℝ) (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    simp only [LinearMap.restrictScalars_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    rw [show inner ℂ u (z : EuclideanSpace ℂ (Fin n)) = 0 from hz, smul_zero]
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere s = 0 := by
    rw [Measure.toSphere_apply' _ hs]
    rw [measure_mono_null hsub (Measure.addHaar_submodule _ P hP), mul_zero]
  simp [sphereProb, ProbabilityTheory.cond, h0]
end ReciprocityTheory.MultiplicativeHeights
