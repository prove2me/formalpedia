-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.card_elementarySubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:52.751804+00:00
-- url     : https://prove2.me/submissions/ff05266b-4f5d-47d6-8231-dcc557920678

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
theorem _root_.solution {p a : ℕ} [Fact p.Prime]
    (Q : Subgroup (Multiplicative (Fin a → ZMod p))) :
    Nat.card Q =
      p ^ Module.finrank (ZMod p) (elementarySubgroupSubmoduleIso p a Q) := by
  letI : Fintype (elementarySubgroupSubmoduleIso p a Q) := Fintype.ofFinite _
  rw [Nat.card_congr (elementaryCarrierEquiv p a Q)]
  rw [Nat.card_eq_fintype_card]
  simpa using (Module.card_eq_pow_finrank (K := ZMod p)
    (V := elementarySubgroupSubmoduleIso p a Q))
end SharpIntermediateSubgroupBounds
