-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.intermediateSubgroups_card_le_totalQBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:01:31.509075+00:00
-- url     : https://prove2.me/submissions/f776e173-8648-4b80-90bc-52a1a41b86b0

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_primePowerLayer_card_le

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p a : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hindex : H.index = p ^ a) :
    (intermediateSubgroups H).card ≤ totalQBinom p a := by
  classical
  let layers : Finset (Subgroup G) :=
    (Finset.range (a + 1)).biUnion fun k ↦ primePowerLayer p k H ⊤
  have hcover : intermediateSubgroups H ⊆ layers := by
    intro K hK
    have hHK := mem_intermediateSubgroups.mp hK
    have hdvd : K.index ∣ p ^ a := by
      rw [← hindex]
      exact H.index_dvd_of_le hHK
    obtain ⟨k, hk, hkindex⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_range.mpr (by omega), mem_primePowerLayer.mpr
      ⟨hHK, le_top, by simpa using hkindex⟩⟩
  calc
    (intermediateSubgroups H).card ≤ layers.card := Finset.card_le_card hcover
    _ ≤ ∑ k ∈ Finset.range (a + 1), (primePowerLayer p k H ⊤).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (a + 1), qBinom p a k := by
      exact Finset.sum_le_sum fun k _ ↦ primePowerLayer_card_le hp H hindex
    _ = totalQBinom p a := by
      rw [totalQBinom, Fin.sum_univ_eq_sum_range]
end SharpIntermediateSubgroupBounds
