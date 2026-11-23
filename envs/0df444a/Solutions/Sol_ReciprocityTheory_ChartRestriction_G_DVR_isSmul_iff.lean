-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:49.256635+00:00
-- url     : https://prove2.me/submissions/56788d90-9a06-48a6-9522-7ba9d161ad7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
  [Algebra (FractionRing R) F]
variable {D F} {k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (ζ : F) (s s' : Fam D F k) : Fam.IsSmul D F ζ s s' ↔ s' = ζ • s := by
  constructor
  · intro h
    exact fam_ext fun α j => h α j
  · rintro rfl α j
    rfl
end ReciprocityTheory.ChartRestriction.G.DVR
