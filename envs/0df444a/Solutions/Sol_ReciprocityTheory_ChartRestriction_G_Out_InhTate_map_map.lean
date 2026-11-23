-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.InhTate.map_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:35.129339+00:00
-- url     : https://prove2.me/submissions/f8325e98-8661-49b0-a0ad-40dd0f707bd2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.InhTate
open Semi Inh
namespace ReciprocityTheory.ChartRestriction.G.Out.InhTate
theorem _root_.solution {Y : Scheme.{0}} {U V W : Y.Opens} (h : W ≤ V) (h' : V ≤ U) (y : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((Y.presheaf.map (homOfLE h').op).hom y) =
      (Y.presheaf.map (homOfLE (h.trans h')).op).hom y :=
  map_map_lemma h h' y
end ReciprocityTheory.ChartRestriction.G.Out.InhTate
