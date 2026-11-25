-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.toSphere_map_sphereMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:20:27.661869+00:00
-- url     : https://prove2.me/submissions/390ba366-9eda-4322-a669-c7ccf7ca1bbf

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_MeasurePreservingSphereMap
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_continuous_sphereMap

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
theorem _root_.solution {n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    Measure.map (sphereMap U) (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere =
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hmeas := (continuous_sphereMap U).measurable
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hset : (Set.Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap U ⁻¹' s) :
      Set (EuclideanSpace ℂ (Fin n)))) = U ⁻¹' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, U z, ⟨sphereMap U z, hz, rfl⟩, (map_smul U r (z : EuclideanSpace ℂ (Fin n))).symm⟩
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hxy⟩
      refine ⟨r, hr, U.symm z, ⟨sphereMap U.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap U (sphereMap U.symm z) = z := Subtype.ext (by simp [sphereMap])
        rw [this]; exact hz
      · rw [← map_smul, hxy]; simp
  rw [hset]
  have hU : MeasurePreserving (U.toHomeomorph.toMeasurableEquiv) volume volume :=
    U.measurePreserving
  exact hU.measure_preimage_equiv _
end ReciprocityTheory.MultiplicativeHeights
