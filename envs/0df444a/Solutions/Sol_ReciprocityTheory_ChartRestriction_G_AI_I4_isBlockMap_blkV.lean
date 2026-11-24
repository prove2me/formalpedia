-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I4.isBlockMap_blkV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:58.671272+00:00
-- url     : https://prove2.me/submissions/1163a22d-3359-4255-b5b8-6d28c1cfa0ca

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_GenericFibreKerTarget

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.AI.I4
theorem _root_.solution (κ : Type*) (b : Fin 2) :
    IsBlockMap (ι := fun _ : Unit => κ) (ι' := fun _ : Fin 2 => κ) (blkOf b) (blkV κ b) := by
  refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨u, i⟩ ⟨u', i'⟩ h
    cases u; cases u'
    cases h
    rfl
  · rintro ⟨k', i⟩ ⟨u, rfl⟩
    exact ⟨⟨u, i⟩, rfl⟩
end ReciprocityTheory.ChartRestriction.G.AI.I4
