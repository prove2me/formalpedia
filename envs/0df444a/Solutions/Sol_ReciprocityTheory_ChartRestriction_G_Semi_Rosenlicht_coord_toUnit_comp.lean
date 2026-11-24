-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_toUnit_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:53.945083+00:00
-- url     : https://prove2.me/submissions/be1b3f07-97ef-4d6f-9588-2a39c417aff0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_coord_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_toUnit_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
variable {S : Scheme.{u}}
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution (Z : Over S) {Y : Type u} [AddCommGroup Y]
    (e : 𝟙_ (Over S) ⟶ splitTorus S Y) (x : torusRing ZU Y) :
    (coord (toUnit Z ≫ e)).hom x = Z.hom.appTop.hom ((coord e).hom x) := by
  rw [coord_comp]
  first
  | exact congrArg (fun f => Scheme.Hom.appTop f |>.hom ((coord e).hom x)) (toUnit_left Z)
  | (rw [CommRingCat.comp_apply, toUnit_left])
  | (simp [toUnit_left]; done)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
