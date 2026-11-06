-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.schemeModuleGlobalIsoPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:17.162195+00:00
-- url     : https://prove2.me/submissions/b196d71b-d1a3-462b-bb8b-830d7fab6076

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeModulePair_restrictions_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (hcover : U ⊔ V = ⊤) :
    Function.Injective (schemeModuleGlobalIsoPair M U V e f) := by
  intro s t h
  apply schemeModulePair_restrictions_injective M U V hcover
  apply Prod.ext
  · have hh := congrArg (fun a : A => e.inv a) (congrArg Prod.fst h)
    exact (Iso.hom_inv_id_apply e _).symm.trans (hh.trans (Iso.hom_inv_id_apply e _))
  · have hh := congrArg (fun b : B => f.inv b) (congrArg Prod.snd h)
    exact (Iso.hom_inv_id_apply f _).symm.trans (hh.trans (Iso.hom_inv_id_apply f _))
end QEC.Coding.AlgebraicGeometry
