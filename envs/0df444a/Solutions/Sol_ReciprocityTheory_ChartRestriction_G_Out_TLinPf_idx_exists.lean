-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.idx_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:57.642293+00:00
-- url     : https://prove2.me/submissions/0084d4f6-0244-4809-be2e-c0b75cda8f84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart

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
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Y) :
    ∃ idx : (Y ⟶ X) → L.ι, ∀ ψ, ψ.base y ∈ L.U (idx ψ) :=
  ⟨fun ψ => (exists_chart L hL (ψ.base y)).choose,
   fun ψ => (exists_chart L hL (ψ.base y)).choose_spec⟩
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
