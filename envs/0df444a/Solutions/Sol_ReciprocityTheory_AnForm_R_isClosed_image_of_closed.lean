-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isClosed_image_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:45.258337+00:00
-- url     : https://prove2.me/submissions/33f5621f-8984-44fa-bb62-d0e5f20a1647

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) [LocallyOfFiniteType s] [LocallyOfFiniteType t] (x : S)
    (hc : IsClosed ({x} : Set S)) : IsClosed ({g.base x} : Set T) := by
  haveI : JacobsonSpace T := AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace t
  haveI : AlgebraicGeometry.LocallyOfFiniteType (g ≫ t) := by rw [hg]; infer_instance
  haveI : AlgebraicGeometry.LocallyOfFiniteType g := AlgebraicGeometry.locallyOfFiniteType_of_comp g t
  have hx : x ∈ closedPoints S := by simpa [mem_closedPoints_iff] using hc
  have := g.closePoints_subset_preimage_closedPoints hx
  simpa [mem_closedPoints_iff] using this
end ReciprocityTheory.AnForm.R
