-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.isIso_appTop_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:09.090929+00:00
-- url     : https://prove2.me/submissions/2cf87ee7-a5eb-4d33-a6d9-490fd967c93e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_cr_iso_bij

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution {A B : Scheme.{u}} (e : A ≅ B) : Function.Bijective e.hom.appTop.hom := by
  first
  | exact cr_iso_bij (Scheme.Γ.mapIso e.op)
  | exact ConcreteCategory.bijective_of_isIso e.hom.appTop
  | exact cr_iso_bij (asIso e.hom.appTop)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
