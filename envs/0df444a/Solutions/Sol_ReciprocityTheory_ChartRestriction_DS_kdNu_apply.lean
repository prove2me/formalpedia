-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kdNu_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:09:31.554337+00:00
-- url     : https://prove2.me/submissions/bcf4e76e-a7b6-4424-bec0-b3583044f7d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_KDensC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {E X : Type*} [TopologicalSpace E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {m : Measure X} {f : E → X} {U : Set E} (hU : MeasurableSet U) (hf : ContinuousOn f U)
    (hinj : InjOn f U) {A : Set E} (hA : MeasurableSet A) : kdNu m f U A = m (f '' (A ∩ U)) := by
  have hI : Function.Injective (fun x : U => f x) := fun a b h => Subtype.ext (hinj a.2 b.2 h)
  have hM : ∀ s : Set U, MeasurableSet s → MeasurableSet ((fun x : U => f x) '' s) := by
    intro s hs
    have e : (fun x : U => f x) '' s = f '' (Subtype.val '' s) := by rw [image_image]
    rw [e]
    have hsub : Subtype.val '' s ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    exact (hU.subtype_image hs).image_of_continuousOn_injOn (hf.mono hsub) (hinj.mono hsub)
  rw [kdNu, Measure.map_apply measurable_subtype_coe hA,
    Measure.comap_apply _ hI hM _ (measurable_subtype_coe hA)]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x, hx⟩, hxA, rfl⟩; exact ⟨x, ⟨hxA, hx⟩, rfl⟩
  · rintro ⟨x, ⟨hxA, hx⟩, rfl⟩; exact ⟨⟨x, hx⟩, hxA, rfl⟩
end ReciprocityTheory.ChartRestriction.DS
