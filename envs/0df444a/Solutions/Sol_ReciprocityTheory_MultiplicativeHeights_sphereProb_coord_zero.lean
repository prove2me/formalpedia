-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sphereProb_coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:57.57704+00:00
-- url     : https://prove2.me/submissions/e1c722f1-f4b1-4bc0-beff-d0fa78730d38

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC

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
theorem _root_.solution {n : ℕ} (j : Fin n) :
    sphereProb n {z | spherePoint z j = 0} = 0 := by
  let W : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    LinearMap.ker ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).toLinearMap
  have hW : W ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single j (1 : ℂ) ∈ W := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hmem
    change WithLp.ofLp (EuclideanSpace.single j (1 : ℂ)) j = 0 at hmem
    simp at hmem
  have hW0 : (volume : Measure (EuclideanSpace ℂ (Fin n))) (W : Set (EuclideanSpace ℂ (Fin n))) = 0 :=
    Measure.addHaar_submodule _ W hW
  have hmeas : MeasurableSet {z : UnitSphereC n | spherePoint z j = 0} := by
    have hc : Continuous fun z : UnitSphereC n => spherePoint z j := by
      exact (continuous_apply j).comp ((EuclideanSpace.equiv (Fin n) ℂ).continuous.comp
        continuous_subtype_val)
    exact (isClosed_singleton.preimage hc).measurableSet
  have hS : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | spherePoint z j = 0} = 0 := by
    rw [Measure.toSphere_apply' (μ := volume) hmeas]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hW0)
    rintro x ⟨r, -, _, ⟨z, hz, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, spherePoint] at hz
    show ((EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ)
      (r • (z : EuclideanSpace ℂ (Fin n))) = 0
    rw [map_smul]
    show r • WithLp.ofLp (z : EuclideanSpace ℂ (Fin n)) j = 0
    rw [hz, smul_zero]
  simp only [sphereProb, ProbabilityTheory.cond, Measure.restrict_univ, Measure.smul_apply,
    smul_eq_mul, hS, mul_zero]
end ReciprocityTheory.MultiplicativeHeights
