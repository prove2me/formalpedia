-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.measurePreserving_toSphere_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:17:46.753811+00:00
-- url     : https://prove2.me/submissions/92c7e66d-3ee6-4e26-b672-18e66dd0dd22

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
private theorem volume_preimage_linearIsometryEquiv {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n))
    (X : Set (EuclideanSpace ℂ (Fin n))) : volume (A ⁻¹' X) = volume X :=
  A.measurePreserving.measure_preimage_emb A.toHomeomorph.measurableEmbedding X
private theorem Ioo_smul_image_preimage_sphere_eq_preimage {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) (s : Set (UnitSphereC n)) :
    Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((fun z : UnitSphereC n =>
        (⟨A z, by simp⟩ : UnitSphereC n)) ⁻¹' s)) =
      A ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨r, hr, _, ⟨⟨A z, by simp⟩, hz, rfl⟩, ?_⟩
    exact (map_smul A r (z : EuclideanSpace ℂ (Fin n))).symm
  · rintro ⟨r, hr, _, ⟨w, hw, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨A.symm w, by simp⟩, ?_, rfl⟩, ?_⟩
    · have hw' : (⟨A (A.symm (w : EuclideanSpace ℂ (Fin n))), by simp⟩ : UnitSphereC n) = w :=
        Subtype.ext (by simp)
      exact (congrArg (· ∈ s) hw').mpr hw
    · show r • A.symm (w : EuclideanSpace ℂ (Fin n)) = x
      calc r • A.symm (w : EuclideanSpace ℂ (Fin n))
          = A.symm (r • (w : EuclideanSpace ℂ (Fin n))) :=
            (map_smul A.symm r (w : EuclideanSpace ℂ (Fin n))).symm
        _ = x := by rw [hx, LinearIsometryEquiv.symm_apply_apply]
end ReciprocityTheory.MultiplicativeHeights
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n))
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  have hcont : Continuous (fun z : UnitSphereC n => (⟨A z, by simp⟩ : UnitSphereC n)) :=
    (A.continuous.comp continuous_subtype_val).subtype_mk _
  refine ⟨hcont.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hcont.measurable hs, Measure.toSphere_apply' (μ := volume) (hcont.measurable hs),
    Measure.toSphere_apply' (μ := volume) hs, Ioo_smul_image_preimage_sphere_eq_preimage A s,
    volume_preimage_linearIsometryEquiv]
end ReciprocityTheory.MultiplicativeHeights
