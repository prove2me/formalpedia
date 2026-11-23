-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.dI_mset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:52.365668+00:00
-- url     : https://prove2.me/submissions/3b02af29-4851-4d13-a65b-cd130bc47da0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (φ : OpenPartialHomeomorph Z (Fin e → ℂ)) {s : Set Z} (hs : MeasurableSet s) :
    MeasurableSet (φ.target ∩ φ.symm ⁻¹' s) := by
  have hc : Continuous (φ.target.domRestrict φ.symm) := φ.continuousOn_symm.domRestrict
  have h1 := φ.open_target.measurableSet.subtype_image (hc.measurable hs)
  convert h1 using 1
  ext y
  constructor
  · rintro ⟨hy, hs'⟩; exact ⟨⟨y, hy⟩, hs', rfl⟩
  · rintro ⟨⟨y', hy'⟩, hs', rfl⟩; exact ⟨hy', hs'⟩
end ReciprocityTheory.AnForm.M
