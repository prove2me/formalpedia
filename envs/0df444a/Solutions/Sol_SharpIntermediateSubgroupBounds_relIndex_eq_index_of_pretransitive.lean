-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.relIndex_eq_index_of_pretransitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:11.929891+00:00
-- url     : https://prove2.me/submissions/bfe62955-4ca9-44d0-9566-765ded7d68e9

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_pretransitive_quotient_of_le

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Pointwise
noncomputable section
variable {G : Type*} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupCarrierFintype
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupIntervalFintype
attribute [local instance] SharpIntermediateSubgroupBounds.coatomFiberFintype
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {P H K : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) (hHK : H ≤ K) :
    K.relIndex P = K.index := by
  letI : MulAction.IsPretransitive P (G ⧸ K) := pretransitive_quotient_of_le hpre hHK
  have hstab :
      MulAction.stabilizer P ((1 : G) : G ⧸ K) = K.subgroupOf P := by
    ext g
    rw [MulAction.mem_stabilizer_iff]
    have hsmul : g • ((1 : G) : G ⧸ K) = (((g : G) * 1 : G) : G ⧸ K) := rfl
    rw [hsmul, mul_one, QuotientGroup.eq]
    simp only [mul_one, Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
  calc
    K.relIndex P = (K.subgroupOf P).index := rfl
    _ = (MulAction.stabilizer P ((1 : G) : G ⧸ K)).index := by rw [hstab]
    _ = Nat.card (G ⧸ K) := MulAction.index_stabilizer_of_transitive P _
    _ = K.index := rfl
end SharpIntermediateSubgroupBounds
