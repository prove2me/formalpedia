-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.eq_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:33.68009+00:00
-- url     : https://prove2.me/submissions/d9cf43bf-2cfc-4a25-ad67-dc1865d8e61f

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
    (s t : Γ(Y, ⊤))
    (h : ∀ j, (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom s =
      (Y.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op).hom t) : s = t :=
  Y.sheaf.eq_of_locally_eq' U ⊤ (fun j => homOfLE le_top) hc.ge s t h
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
