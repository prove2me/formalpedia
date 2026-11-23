-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.ringHom_ext_ZU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:16.737644+00:00
-- url     : https://prove2.me/submissions/264b0cf0-95a1-46fb-b63b-38caf27e4ef5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext

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
theorem _root_.solution {A Y : Type*} [Semiring A] [AddCommGroup Y]
    {f g : AddMonoidAlgebra (ULift.{u} ℤ) Y →+* A} (h : ∀ y, f (single y 1) = g (single y 1)) :
    f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  exact RingHom.congr_fun (ringHom_uliftInt_ext (f.comp AddMonoidAlgebra.singleZeroRingHom)
    (g.comp AddMonoidAlgebra.singleZeroRingHom)) b
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
