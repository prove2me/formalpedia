-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normal_of_index_eq_prime_of_isPGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:00.077825+00:00
-- url     : https://prove2.me/submissions/a6c39093-5f8c-4948-b7c3-8213ac3f14e4

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
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : p.Prime)
    (hG : IsPGroup p G) (H : Subgroup G) (hindex : H.index = p) : H.Normal := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hcard⟩ := hG.exists_card_eq
  have hc : c ≠ 0 := by
    intro hc
    have hle := Nat.le_of_dvd Nat.card_pos H.index_dvd_card
    rw [hindex, hcard, hc, pow_zero] at hle
    have := hp.one_lt
    omega
  apply H.normal_of_index_eq_minFac_card
  rw [hindex, hcard, hp.pow_minFac hc]
end SharpIntermediateSubgroupBounds
