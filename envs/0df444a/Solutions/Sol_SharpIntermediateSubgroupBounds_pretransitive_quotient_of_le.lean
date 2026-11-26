-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.pretransitive_quotient_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:33.313547+00:00
-- url     : https://prove2.me/submissions/0a23376e-71a4-4f83-b9c6-e8c32bf6663c

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
theorem _root_.solution {P H K : Subgroup G}
    (hpre : MulAction.IsPretransitive P (G ⧸ H)) (hHK : H ≤ K) :
    MulAction.IsPretransitive P (G ⧸ K) := by
  letI : MulAction.IsPretransitive P (G ⧸ H) := hpre
  refine ⟨?_⟩
  rintro ⟨g⟩ ⟨g'⟩
  obtain ⟨p, hp'⟩ := MulAction.exists_smul_eq P ((g : G) : G ⧸ H) ((g' : G) : G ⧸ H)
  refine ⟨p, ?_⟩
  apply QuotientGroup.eq.mpr
  exact hHK (QuotientGroup.eq.mp hp')
end SharpIntermediateSubgroupBounds
