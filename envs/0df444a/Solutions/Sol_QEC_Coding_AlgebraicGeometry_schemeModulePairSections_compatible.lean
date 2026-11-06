-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModulePairSections_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:25.904694+00:00
-- url     : https://prove2.me/submissions/29687736-adb7-4014-b205-74fdd5c1f7ce

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (s : Γ(M, U)) (t : Γ(M, V))
    (h : M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s =
      M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) :
    TopCat.Presheaf.IsCompatible M.presheaf (schemeModulePairOpens U V)
      (schemeModulePairSections M U V s t) := by
  intro b d
  cases b <;> cases d
  · rfl
  · exact h
  · let i : V ⊓ U ⟶ U ⊓ V := eqToHom (inf_comm V U)
    have hr := congrArg (fun z => M.presheaf.map i.op z) h
    have hs : M.presheaf.map i.op
        (M.presheaf.map (TopologicalSpace.Opens.infLELeft U V).op s) =
        M.presheaf.map (TopologicalSpace.Opens.infLERight V U).op s := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rfl
    have ht : M.presheaf.map i.op
        (M.presheaf.map (TopologicalSpace.Opens.infLERight U V).op t) =
        M.presheaf.map (TopologicalSpace.Opens.infLELeft V U).op t := by
      rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
      rfl
    exact (ht.symm.trans hr.symm).trans hs
  · rfl
end QEC.Coding.AlgebraicGeometry
