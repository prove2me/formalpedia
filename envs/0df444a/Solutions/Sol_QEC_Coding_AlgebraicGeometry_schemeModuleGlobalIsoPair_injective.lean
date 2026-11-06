-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.schemeModuleGlobalIsoPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:35:36.75622+00:00
-- url     : https://prove2.me/submissions/d14c2873-6de0-4cf8-903e-752a638b758d

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_ModulePairDescent
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U V : X.Opens)
variable {A B : AddCommGrpCat.{u}} (e : Γ(M, U) ≅ A) (f : Γ(M, V) ≅ B)

theorem solution (hcover : U ⊔ V = ⊤) :
    Function.Injective (schemeModuleGlobalIsoPair M U V e f) := by
  intro x y hxy
  apply (schemeModuleAbelianSheaf M).eq_of_locally_eq₂
    (homOfLE le_top) (homOfLE le_top) hcover.ge
  · exact (ConcreteCategory.bijective_of_isIso e.hom).injective (congrArg Prod.fst hxy)
  · exact (ConcreteCategory.bijective_of_isIso f.hom).injective (congrArg Prod.snd hxy)
