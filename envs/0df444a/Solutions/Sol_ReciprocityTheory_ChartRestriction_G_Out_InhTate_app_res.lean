-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.InhTate.app_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:17:08.698979+00:00
-- url     : https://prove2.me/submissions/59bae00d-ac78-4d5f-83aa-97ee62325f91

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Γ(X, ⊤)) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ f ⁻¹ᵁ V) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.app V).hom ((X.presheaf.map (homOfLE le_top).op).hom y)) =
      (Y.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom y) := by
  rw [app_res_lemma_2 f y V, map_map_lemma] <;> rfl
end ReciprocityTheory.ChartRestriction.G.Out.InhTate
