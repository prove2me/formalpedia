-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.primePowerLayer_card_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:59:03.82252+00:00
-- url     : https://prove2.me/submissions/43673874-6ad9-45dc-a583-9c29f25eddd9

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
theorem _root_.solution {p k : ℕ} {T P : Subgroup G} (hTP : T ≤ P) :
    (primePowerLayer p k T P).card =
      (primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P)).card := by
  classical
  let toSubgroup (Q : ↑(primePowerLayer p k T P)) :
      ↑(primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P)) := by
    refine ⟨Q.1.subgroupOf P, ?_⟩
    have hQ := (mem_primePowerLayer.mp Q.2)
    apply mem_primePowerLayer.mpr
    refine ⟨Subgroup.comap_mono hQ.1, le_top, ?_⟩
    simpa using
      (Subgroup.relIndex_subgroupOf (H := Q.1) (K := P) (L := P) le_rfl).trans hQ.2.2
  let fromSubgroup (R : ↑(primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P))) :
      ↑(primePowerLayer p k T P) := by
    refine ⟨R.1.map P.subtype, ?_⟩
    have hR := mem_primePowerLayer.mp R.2
    apply mem_primePowerLayer.mpr
    refine ⟨?_, Subgroup.map_subtype_le R.1, ?_⟩
    · calc
        T = Subgroup.map P.subtype (T.subgroupOf P) :=
          (Subgroup.map_subgroupOf_eq_of_le hTP).symm
        _ ≤ Subgroup.map P.subtype R.1 := Subgroup.map_mono hR.1
    · have hi := Subgroup.relIndex_map_map_of_injective R.1 (⊤ : Subgroup P)
          P.subtype_injective
      have htop : Subgroup.map P.subtype (⊤ : Subgroup P) = P := by
        rw [← P.subtype.range_eq_map, Subgroup.range_subtype]
      rw [htop] at hi
      exact hi.trans hR.2.2
  have hleft (Q : ↑(primePowerLayer p k T P)) : fromSubgroup (toSubgroup Q) = Q := by
    apply Subtype.ext
    exact Subgroup.map_subgroupOf_eq_of_le (mem_primePowerLayer.mp Q.2).2.1
  have hright (R : ↑(primePowerLayer p k (T.subgroupOf P) (⊤ : Subgroup P))) :
      toSubgroup (fromSubgroup R) = R := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective R.1
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr
    { toFun := toSubgroup
      invFun := fromSubgroup
      left_inv := hleft
      right_inv := hright }
end SharpIntermediateSubgroupBounds
