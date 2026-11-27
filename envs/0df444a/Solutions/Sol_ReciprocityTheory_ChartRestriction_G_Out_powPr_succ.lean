-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.powPr_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:26:35.989437+00:00
-- url     : https://prove2.me/submissions/cbc1285c-098f-4c37-bf4d-db2e47014d3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {S : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Out
theorem _root_.solution (G : Over S) (n : ℕ) (i : Fin n) :
    powPr G (n := n + 1) i.succ = snd _ _ ≫ powPr G i := rfl
end ReciprocityTheory.ChartRestriction.G.Out
