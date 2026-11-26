-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.coatomFiber_card_le_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:03.273459+00:00
-- url     : https://prove2.me/submissions/35c4a6f9-c31b-4c4e-adad-a26d279defad

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (M V : Subgroup G) [M.Normal]
    (hM : IsCoatom M) (hVM : V ≤ M) :
    Fintype.card (CoatomFiber M V) ≤ V.relIndex M := by
  classical
  obtain ⟨x, -, hxM⟩ := SetLike.exists_of_lt hM.lt_top
  have sup_eq_top (S : Subgroup G) (hS : ¬ S ≤ M) : S ⊔ M = ⊤ := by
    apply (hM.ne_iff_eq_top le_sup_right).mp
    intro hSM
    exact hS (le_sup_left.trans_eq hSM)
  have exists_rep (Q : CoatomFiber M V) : ∃ m : M, x * (m : G) ∈ Q.1 := by
    have hxQM : x ∈ Q.1 ⊔ M := by
      rw [sup_eq_top Q.1 Q.2.2]
      exact Subgroup.mem_top x
    obtain ⟨q, hq, m, hm, hqmx⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := Q.1) (t := M) (x := x)).mp hxQM
    refine ⟨⟨m⁻¹, M.inv_mem hm⟩, ?_⟩
    rw [← hqmx]
    simpa [mul_assoc] using hq
  let rep : CoatomFiber M V → M := fun Q ↦ Classical.choose (exists_rep Q)
  have rep_mem (Q : CoatomFiber M V) : x * (rep Q : G) ∈ Q.1 :=
    Classical.choose_spec (exists_rep Q)
  have hVQ (Q : CoatomFiber M V) : V ≤ Q.1 := by
    intro v hv
    have hvInf : v ∈ Q.1 ⊓ M := by
      rw [Q.2.1]
      exact hv
    exact hvInf.1
  have generated (Q : CoatomFiber M V) :
      V ⊔ Subgroup.closure {x * (rep Q : G)} = Q.1 := by
    apply le_antisymm
    · refine sup_le (hVQ Q) ((Subgroup.closure_le Q.1).2 ?_)
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact rep_mem Q
    · let R : Subgroup G := V ⊔ Subgroup.closure {x * (rep Q : G)}
      have hRQ : R ≤ Q.1 := by
        refine sup_le (hVQ Q) ((Subgroup.closure_le Q.1).2 ?_)
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact rep_mem Q
      have hqR : x * (rep Q : G) ∈ R :=
        Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _))
      have hqM : x * (rep Q : G) ∉ M := by
        intro h
        apply hxM
        have hmInv : (rep Q : G)⁻¹ ∈ M := M.inv_mem (rep Q).2
        simpa [mul_assoc] using M.mul_mem h hmInv
      have hRnot : ¬ R ≤ M := fun h ↦ hqM (h hqR)
      have hRM : R ⊔ M = ⊤ := sup_eq_top R hRnot
      intro y hy
      have hyRM : y ∈ R ⊔ M := by
        rw [hRM]
        exact Subgroup.mem_top y
      obtain ⟨r, hr, m, hm, hrmy⟩ :=
        (Subgroup.mem_sup_of_normal_right (s := R) (t := M) (x := y)).mp hyRM
      have hmQ : m ∈ Q.1 := by
        have hm_eq : m = r⁻¹ * y := by
          rw [← hrmy]
          simp
        rw [hm_eq]
        exact Q.1.mul_mem (Q.1.inv_mem (hRQ hr)) hy
      have hmV : m ∈ V := by
        rw [← Q.2.1]
        exact ⟨hmQ, hm⟩
      have hmR : m ∈ R := Subgroup.mem_sup_left hmV
      rw [← hrmy]
      exact R.mul_mem hr hmR
  let f : CoatomFiber M V → M ⧸ V.subgroupOf M := fun Q ↦ QuotientGroup.mk (rep Q)
  have fiber_le (A B : CoatomFiber M V) (hf : f A = f B) : B.1 ≤ A.1 := by
    rw [← generated B]
    refine sup_le (hVQ A) ((Subgroup.closure_le A.1).2 ?_)
    rw [Set.singleton_subset_iff]
    have hvM : (rep A)⁻¹ * rep B ∈ V.subgroupOf M := QuotientGroup.eq.mp hf
    have hv : (rep A : G)⁻¹ * (rep B : G) ∈ V := Subgroup.mem_subgroupOf.mp hvM
    have hvA : (rep A : G)⁻¹ * (rep B : G) ∈ A.1 := hVQ A hv
    have hprod := A.1.mul_mem (rep_mem A) hvA
    simpa [mul_assoc] using hprod
  have hf_injective : Function.Injective f := by
    intro A B hf
    apply Subtype.ext
    exact le_antisymm (fiber_le B A hf.symm) (fiber_le A B hf)
  calc
    Fintype.card (CoatomFiber M V) ≤ Fintype.card (M ⧸ V.subgroupOf M) :=
      Fintype.card_le_of_injective f hf_injective
    _ = V.relIndex M := by
      rw [Fintype.card_eq_nat_card]
      rfl
end SharpIntermediateSubgroupBounds
