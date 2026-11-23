-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.ringHom_uliftInt_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:13.275872+00:00
-- url     : https://prove2.me/submissions/08a3c71e-9625-4f81-ad69-0f9b59e4cafe

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
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution {A : Type*} [Semiring A] (f g : ULift.{u} ℤ →+* A) : f = g := by
  first
  | exact Subsingleton.elim f g
  | (ext x
     exact RingHom.congr_fun (RingHom.ext_int (f.comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom)
       (g.comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom)) x.down)
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
