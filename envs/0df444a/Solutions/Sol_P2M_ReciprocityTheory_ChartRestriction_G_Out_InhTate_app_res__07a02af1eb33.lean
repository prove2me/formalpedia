-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_Out_InhTate_app_res__07a02af1eb33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:53:11.176263+00:00
-- url     : https://prove2.me/submissions/6ae4228b-5cfd-4b16-9248-1c4f82407c24

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Γ(X, ⊤)) (V : X.Opens) :
    (f.app V).hom ((X.presheaf.map (homOfLE le_top).op).hom y) =
      (Y.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom y) :=
  app_res_lemma_2 f y V
end ReciprocityTheory.ChartRestriction.G.Out.InhTate
