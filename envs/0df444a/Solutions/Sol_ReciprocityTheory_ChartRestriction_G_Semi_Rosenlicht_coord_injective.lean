-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.coord_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:12.133589+00:00
-- url     : https://prove2.me/submissions/ba812309-0c3e-43d9-a6e0-0dfddba53929

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective

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
theorem _root_.solution {Z : Over S} {Y : Type u} [AddCommGroup Y] {g g' : Z ⟶ splitTorus S Y}
    (h : coord g = coord g') : g = g' := by
  have h1 : (g.left ≫ torusFst S Y).appTop = (g'.left ≫ torusFst S Y).appTop := by
    have h0 := congrArg (fun φ => (Scheme.ΓSpecIso (torusRing ZU Y)).hom ≫ φ) h
    simpa only [coord, Iso.hom_inv_id_assoc] using h0
  have h2 : g.left ≫ torusFst S Y = g'.left ≫ torusFst S Y := by
    first
    | exact ext_of_isAffine h1
    | exact Scheme.ext_of_isAffine h1
    | exact Scheme.Hom.ext_of_isAffine h1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h2
  · exact (Over.w g).trans (Over.w g').symm
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
