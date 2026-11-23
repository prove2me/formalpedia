-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:09.025853+00:00
-- url     : https://prove2.me/submissions/ef4e47cd-4ae3-49ec-b5b8-5fcff652ac56

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback

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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
theorem _root_.solution {Y : Scheme.{0}} {κ : Type} (U : κ → Y.Opens) (hc : ⨆ j, U j = ⊤)
    (f : ∀ j, Γ(Y, U j))
    (h : ∀ i j, (Y.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (f i) =
      (Y.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (f j)) :
    ∃ s : Γ(Y, ⊤), ∀ j, (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom s = f j := by
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun j => homOfLE le_top) hc.ge f h
  exact ⟨s, hs⟩
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
