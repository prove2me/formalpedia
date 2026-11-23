-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Out.TLinPf.padd_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:03.512056+00:00
-- url     : https://prove2.me/submissions/3c1a2ef0-4a87-488c-80cc-8c8e992cd65e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero

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
theorem _root_.solution {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] {T : Over S}
    (x y : T ⟶ B) : padd B x y = padd B y x := by
  unfold padd
  first
  | exact mul_comm x y
  | (rw (occs := .pos [1]) [← IsCommMonObj.mul_comm B]; rw [← Category.assoc]; congr 1; ext <;> simp)
  | rw [Category.id_comp]
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf
