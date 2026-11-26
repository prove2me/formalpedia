-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.intermediate_interval_card_le_totalQBinom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:13.647548+00:00
-- url     : https://prove2.me/submissions/71264adb-0022-4ad9-9e00-52c00c709bf0

import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Atoms
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_PrimePower
import Theorems.Thm_SharpIntermediateSubgroupBounds_intermediateSubgroups_card_eq_Ici
import Theorems.Thm_SharpIntermediateSubgroupBounds_intermediateSubgroups_card_le_totalQBinom

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
    Fintype.card (Set.Ici H) ≤ totalQBinom p a := by
  rw [← intermediateSubgroups_card_eq_Ici]
  exact intermediateSubgroups_card_le_totalQBinom hp H hindex
end SharpIntermediateSubgroupBounds
