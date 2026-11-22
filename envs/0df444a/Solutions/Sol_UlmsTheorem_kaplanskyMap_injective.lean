-- Prove2me | solution 1 for UlmsTheorem.kaplanskyMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:57:31.4735+00:00
-- url     : https://prove2.me/submissions/4dd855e0-e9b4-479f-b289-2c2b333b7d25

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero



set_option autoImplicit true
@[expose] public section
public section
open UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
namespace UlmsTheorem
theorem _root_.solution
    (S : AddSubgroup G) (α : Ordinal) :
    Function.Injective (kaplanskyMap p S α) := by
  apply (AddMonoidHom.ker_eq_bot_iff (kaplanskyMap p S α)).1
  ext x
  change (kaplanskyMap p S α) x = 0 ↔ x = 0
  refine Quotient.inductionOn x ?_
  intro a
  constructor
  · intro ha
    simp only [kaplanskyMap] at ha
    have hrep : (kaplanskySocleRep p S α a : G) ∈
        pSocleAt p (Order.succ α) (G := G) := by
      exact (Submodule.Quotient.mk_eq_zero _).1 ha
    apply (QuotientAddGroup.eq_zero_iff _).2
    change (a : G) ∈ stageAt p S (Order.succ α)
    refine ⟨a.property.1, ?_⟩
    have ha :
        (a : G) =
          (kaplanskySocleRep p S α a : G) +
            kaplanskyCorrection p S α a := by
      change (a : G) =
        ((a : G) - kaplanskyCorrection p S α a) +
          kaplanskyCorrection p S α a
      abel
    rw [ha]
    exact (ulmSubgroup p (Order.succ α)).add_mem hrep.2
      (kaplanskyCorrection_mem p S α a)
  · intro ha
    rw [ha]
    exact map_zero (kaplanskyMap p S α)
end UlmsTheorem
