-- Prove2me | solution 2 for ReciprocityTheory.ChartRestriction.G.DVR.TG.map_inj_of_le_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:38.930529+00:00
-- url     : https://prove2.me/submissions/b238aeda-932a-4721-acf5-50c84de6e29e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
namespace ReciprocityTheory.ChartRestriction.G.DVR.TG
theorem _root_.solution {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  obtain rfl : W = V := le_antisymm h1 h2
  have e : homOfLE h1 = 𝟙 W := Subsingleton.elim _ _
  rw [e] at h
  simpa using h
end ReciprocityTheory.ChartRestriction.G.DVR.TG
