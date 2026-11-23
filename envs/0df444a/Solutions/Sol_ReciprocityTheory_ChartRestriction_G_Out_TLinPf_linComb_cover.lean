-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.linComb_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:34.922634+00:00
-- url     : https://prove2.me/submissions/e9010493-86b6-4e8d-982d-25d83774bf4e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_idx_exists

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
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : ⨆ j, (LB.LinComb L φ ε).U j = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨idx, hidx⟩ := idx_exists L hL y
  exact TopologicalSpace.Opens.mem_iSup.2
    ⟨fun k => idx (φ k), Set.mem_iInter.2 fun k => hidx (φ k)⟩
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
