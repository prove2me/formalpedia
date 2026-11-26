-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.isCoatom_of_prime_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:51.483824+00:00
-- url     : https://prove2.me/submissions/c49587e8-663a-4af4-bbf8-9cd12a7719e6

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
theorem _root_.solution (H : Subgroup G) (hprime : H.index.Prime) : IsCoatom H := by
  refine ⟨?_, ?_⟩
  · intro htop
    exact hprime.ne_one (by simp [htop])
  · intro K hHK
    have hdvd : K.index ∣ H.index := H.index_dvd_of_le hHK.le
    rcases hprime.eq_one_or_self_of_dvd K.index hdvd with hK | hK
    · exact Subgroup.index_eq_one.mp hK
    · have htower := H.relIndex_mul_index hHK.le
      have hrel : H.relIndex K = 1 := by
        apply Nat.mul_right_cancel
          (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := H)))
        simpa [hK] using htower
      exact ((not_le_of_gt hHK) (Subgroup.relIndex_eq_one.mp hrel)).elim
end SharpIntermediateSubgroupBounds
