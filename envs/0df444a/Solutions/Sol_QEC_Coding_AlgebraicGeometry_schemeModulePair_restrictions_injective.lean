-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModulePair_restrictions_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:58:37.008203+00:00
-- url     : https://prove2.me/submissions/c0529ad6-22bf-4db2-af62-b0b0afd7e573

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
theorem _root_.solution (hcover : U ⊔ V = ⊤) :
    Function.Injective (fun z : Γ(M, ⊤) =>
      ((M.presheaf.map (homOfLE le_top).op z,
       M.presheaf.map (homOfLE le_top).op z) : Γ(M,U) × Γ(M,V))) := by
  intro s t h
  exact (schemeModuleAbelianSheaf M).eq_of_locally_eq₂
    (homOfLE le_top) (homOfLE le_top) (by rw [hcover]) s t
    (congrArg Prod.fst h) (congrArg Prod.snd h)
end QEC.Coding.AlgebraicGeometry
