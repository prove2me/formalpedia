-- Prove2me | solution 1 for UlmsTheorem.kaplanskyMap_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:58:10.160658+00:00
-- url     : https://prove2.me/submissions/7724a176-5c31-4681-b041-37f168793280

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
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_succ
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
    LinearMap.range (kaplanskyLinearMap p S α (kaplanskyMap p S α)) =
      relativeOccupiedSubmodule p S α := by
  ext z
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro a
    change (ulmDenSubmodule p α).mkQ (kaplanskySocleRep p S α a) ∈
      relativeOccupiedSubmodule p S α
    apply (Submodule.mem_map).2
    refine ⟨kaplanskySocleRep p S α a, ?_, rfl⟩
    change (kaplanskySocleRep p S α a : G) ∈
      pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
    refine ⟨(kaplanskySocleRep p S α a).property, ?_⟩
    change (a : G) - kaplanskyCorrection p S α a ∈
      S ⊔ ulmSubgroup p (Order.succ α)
    simpa [sub_eq_add_neg] using AddSubgroup.add_mem_sup a.property.1
      ((ulmSubgroup p (Order.succ α)).neg_mem
        (kaplanskyCorrection_mem p S α a))
  · intro hz
    obtain ⟨v, hv, rfl⟩ := (Submodule.mem_map).1 hz
    change (v : G) ∈ pSocleAt p α ⊓
      (S ⊔ ulmSubgroup p (Order.succ α)) at hv
    obtain ⟨s, hs, g, hg, hsg⟩ := AddSubgroup.mem_sup.mp hv.2
    have hs_eq : s = (v : G) - g := by
      rw [← hsg]
      abel
    let a : kaplanskyStar p S α := ⟨s, hs, by
      rw [hs_eq]
      exact (ulmSubgroup p α).sub_mem v.property.2
        (ulmSubgroup_antitone p (Order.le_succ α) hg), by
      rw [hs_eq, smul_sub]
      have hvp : p • (v : G) = 0 := v.property.1
      rw [hvp]
      have hpg : p • g ∈ ulmSubgroup p (Order.succ (Order.succ α)) := by
        rw [ulmSubgroup_succ]
        exact ⟨g, hg, rfl⟩
      simpa only [_root_.zero_sub] using
        (ulmSubgroup p (Order.succ (Order.succ α))).neg_mem hpg⟩
    refine ⟨(QuotientAddGroup.mk' (stageAtSuccInStar p S α)) a, ?_⟩
    change (ulmDenSubmodule p α).mkQ (kaplanskySocleRep p S α a) =
      (ulmDenSubmodule p α).mkQ v
    apply (Submodule.Quotient.eq _).2
    change ((kaplanskySocleRep p S α a - v :
      pSocleAt p α (G := G)) : G) ∈
        pSocleAt p (Order.succ α) (G := G)
    rw [mem_pSocleAt]
    refine ⟨(kaplanskySocleRep p S α a - v).property.1, ?_⟩
    have hc := kaplanskyCorrection_mem p S α a
    have hsum :
        -kaplanskyCorrection p S α a - g ∈
          ulmSubgroup p (Order.succ α) :=
      (ulmSubgroup p (Order.succ α)).sub_mem
        ((ulmSubgroup p (Order.succ α)).neg_mem hc) hg
    change (s - kaplanskyCorrection p S α a) - (v : G) ∈
      ulmSubgroup p (Order.succ α)
    rw [← hsg]
    convert hsum using 1
    abel
end UlmsTheorem
