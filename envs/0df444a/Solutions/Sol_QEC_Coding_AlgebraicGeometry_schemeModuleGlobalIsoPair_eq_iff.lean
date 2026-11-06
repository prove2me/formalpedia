-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModuleGlobalIsoPair_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:25:18.096403+00:00
-- url     : https://prove2.me/submissions/b72b2fdc-f0fa-4e8e-977f-b61340b1c49a

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
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (z : Γ(M, ⊤)) (a : A) (b : B) :
    schemeModuleGlobalIsoPair M U V e f z = (a, b) ↔
    M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op z = e.inv a ∧
      M.presheaf.map (homOfLE le_top : V ⟶ ⊤).op z = f.inv b := by
  constructor
  · intro h
    have he := congrArg (fun t : A × B => e.inv t.1) h
    have hf := congrArg (fun t : A × B => f.inv t.2) h
    exact ⟨(Iso.hom_inv_id_apply e _).symm.trans he,
      (Iso.hom_inv_id_apply f _).symm.trans hf⟩
  · rintro ⟨he, hf⟩
    apply Prod.ext
    · exact (congrArg e.hom he).trans (Iso.inv_hom_id_apply e a)
    · exact (congrArg f.hom hf).trans (Iso.inv_hom_id_apply f b)
end QEC.Coding.AlgebraicGeometry
