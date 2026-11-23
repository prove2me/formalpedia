-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.over_appTop_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:09.743996+00:00
-- url     : https://prove2.me/submissions/69dd0351-17fb-4818-bd25-3dea291e6977

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_appTop_comp_apply

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
theorem _root_.solution {W Z V : Over S} (p : W ⟶ Z) (q : Z ⟶ V) (x : Γ(V.left, ⊤)) :
    p.left.appTop.hom (q.left.appTop.hom x) = (p ≫ q).left.appTop.hom x := by
  first
  | exact (appTop_comp_apply p.left q.left x).symm
  | (rw [Over.comp_left, appTop_comp_apply])
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
