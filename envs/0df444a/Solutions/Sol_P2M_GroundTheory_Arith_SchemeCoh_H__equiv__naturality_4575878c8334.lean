-- Prove2me | solution 1 for P2M_GroundTheory_Arith_SchemeCoh_H__equiv__naturality_4575878c8334
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:34:08.482016+00:00
-- url     : https://prove2.me/submissions/ef9cffa5-615b-4bff-b491-e8f1e958d401

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeSheafHomAddEquiv_naturality
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cohomologyPresheafFunctor_map_app_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
namespace GroundTheory.Arith.SchemeCoh
namespace H'
theorem _root_.solution {F G : Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G) (U : C)
    (x : F.H' 0 U) :
    H'.equiv₀ G U (((Sheaf.cohomologyPresheafFunctor J 0).map φ).app (op U) x) =
      φ.hom.app (op U) (H'.equiv₀ F U x) := by
  rw [cohomologyPresheafFunctor_map_app_apply]
  obtain ⟨g, rfl⟩ := (Ext.addEquiv₀ (X := freeSheaf J U) (Y := F)).symm.surjective x
  change freeSheafHomAddEquiv U G (Ext.addEquiv₀ ((Ext.addEquiv₀.symm g).comp (Ext.mk₀ φ)
      (add_zero 0))) = φ.hom.app (op U) (freeSheafHomAddEquiv U F
        (Ext.addEquiv₀ (Ext.addEquiv₀.symm g)))
  rw [AddEquiv.apply_symm_apply, ← freeSheafHomAddEquiv_naturality, Ext.addEquiv₀_symm_apply,
    Ext.mk₀_comp_mk₀]
  congr 1
  apply (Ext.mk₀_bijective _ _).injective
  simp
end H'
end GroundTheory.Arith.SchemeCoh
