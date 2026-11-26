-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.primePowerLayer_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:50.577128+00:00
-- url     : https://prove2.me/submissions/7a4bd45e-4bf0-404e-9b4a-666bdf9508dd

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_pGroup_primePowerLayer_card_le
import Theorems.Thm_SharpIntermediateSubgroupBounds_exists_sylow_pretransitive_of_index_primePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_relIndex_eq_index_of_pretransitive
import Theorems.Thm_SharpIntermediateSubgroupBounds_subgroupOf_injective_of_pretransitive

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a k : ℕ} (hp : p.Prime) (H : Subgroup G)
    (hindex : H.index = p ^ a) :
    (primePowerLayer p k H ⊤).card ≤ qBinom p a k := by
  classical
  obtain ⟨P, hpre, hrel⟩ := exists_sylow_pretransitive_of_index_primePower hp H hindex
  let target := primePowerLayer p k (H.subgroupOf (P : Subgroup G)) (⊤ : Subgroup P)
  let source := primePowerLayer p k H ⊤
  have hmaps : (source : Set (Subgroup G)).MapsTo (fun K ↦ K.subgroupOf (P : Subgroup G)) target := by
    intro K hK
    have hKl := mem_primePowerLayer.mp hK
    apply mem_primePowerLayer.mpr
    refine ⟨Subgroup.comap_mono hKl.1, le_top, ?_⟩
    have hKi : K.index = p ^ k := by simpa using hKl.2.2
    have hKP : K.relIndex (P : Subgroup G) = p ^ k :=
      (relIndex_eq_index_of_pretransitive hpre hKl.1).trans hKi
    simpa using
      (Subgroup.relIndex_subgroupOf (H := K) (K := (P : Subgroup G))
        (L := (P : Subgroup G)) le_rfl).trans hKP
  have hinj : (source : Set (Subgroup G)).InjOn (fun K ↦ K.subgroupOf (P : Subgroup G)) :=
    (subgroupOf_injective_of_pretransitive hpre).mono fun _ h ↦
      (mem_primePowerLayer.mp h).1
  calc
    source.card ≤ target.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ qBinom p a k := pGroup_primePowerLayer_card_le hp P.2
      (H.subgroupOf (P : Subgroup G)) hrel k
end SharpIntermediateSubgroupBounds
