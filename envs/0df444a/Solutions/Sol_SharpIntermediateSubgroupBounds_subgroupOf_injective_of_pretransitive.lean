-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.subgroupOf_injective_of_pretransitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:38.701964+00:00
-- url     : https://prove2.me/submissions/905d863b-b077-4389-ae8f-b2565445a5c2

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
theorem _root_.solution {P H : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) :
    Set.InjOn (fun K : Subgroup G ↦ K.subgroupOf P) (Set.Ici H) := by
  letI : MulAction.IsPretransitive P (G ⧸ H) := hpre
  intro K hHK L hHL heq
  change K.subgroupOf P = L.subgroupOf P at heq
  apply le_antisymm
  · intro g hgK
    obtain ⟨p, hp⟩ :=
      MulAction.exists_smul_eq P (((1 : G) : G ⧸ H)) ((g : G) : G ⧸ H)
    have hsmul : p • ((1 : G) : G ⧸ H) = (((p : G) * 1 : G) : G ⧸ H) := rfl
    rw [hsmul, mul_one] at hp
    have hpgH : (p : G)⁻¹ * g ∈ H := QuotientGroup.eq.mp hp
    have hpgK : (p : G)⁻¹ * g ∈ K := hHK hpgH
    have hpK : (p : G) ∈ K := by
      have := K.mul_mem hgK (K.inv_mem hpgK)
      simpa [mul_assoc] using this
    have hpL : (p : G) ∈ L := by
      have hpSub : p ∈ K.subgroupOf P := hpK
      rw [heq] at hpSub
      exact hpSub
    have hpgL : (p : G)⁻¹ * g ∈ L := hHL hpgH
    have := L.mul_mem hpL hpgL
    simpa [mul_assoc] using this
  · intro g hgL
    obtain ⟨p, hp⟩ :=
      MulAction.exists_smul_eq P (((1 : G) : G ⧸ H)) ((g : G) : G ⧸ H)
    have hsmul : p • ((1 : G) : G ⧸ H) = (((p : G) * 1 : G) : G ⧸ H) := rfl
    rw [hsmul, mul_one] at hp
    have hpgH : (p : G)⁻¹ * g ∈ H := QuotientGroup.eq.mp hp
    have hpgL : (p : G)⁻¹ * g ∈ L := hHL hpgH
    have hpL : (p : G) ∈ L := by
      have := L.mul_mem hgL (L.inv_mem hpgL)
      simpa [mul_assoc] using this
    have hpK : (p : G) ∈ K := by
      have hpSub : p ∈ L.subgroupOf P := hpL
      rw [← heq] at hpSub
      exact hpSub
    have hpgK : (p : G)⁻¹ * g ∈ K := hHK hpgH
    have := K.mul_mem hpK hpgK
    simpa [mul_assoc] using this
end SharpIntermediateSubgroupBounds
