-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht.torus_const_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.295799+00:00
-- url     : https://prove2.me/submissions/a5040073-af2c-4933-bf80-f22273ca6dad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_cr_iso_bij
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_torusGamma_const

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
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]
namespace ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
theorem _root_.solution :
    Function.Injective (splitTorus (Spec (.of K)) X).hom.appTop.hom := by
  intro c₁ c₂ h
  have h' := congrArg (torusGamma K X).hom h
  rw [torusGamma_const, torusGamma_const] at h'
  first
  | exact (cr_iso_bij (Scheme.ΓSpecIso (.of K))).1 (AddMonoidAlgebra.single_injective (0 : X) h')
  | exact (cr_iso_bij (Scheme.ΓSpecIso (.of K))).1 (by simpa using h')
  | exact (cr_iso_bij (Scheme.ΓSpecIso (.of K))).1 (AddMonoidAlgebra.single_inj.1 h')
end ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
