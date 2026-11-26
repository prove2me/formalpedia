-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.intermediate_unique_band
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:03:09.525879+00:00
-- url     : https://prove2.me/submissions/57c74791-29db-4047-a527-8ca01e6c2061

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (H : Subgroup G) (q : ℕ)
    (hn : 1 < H.index) (hq : 1 < q) (K : interval H) :
    ∃! r : Fin (Nat.log q H.index + 1),
      q ^ (r : ℕ) ≤ H.relIndex K.1 ∧
        H.relIndex K.1 < q ^ ((r : ℕ) + 1) := by
  let m := H.relIndex K.1
  have hm0 : m ≠ 0 := by
    letI : H.IsFiniteRelIndex K.1 := H.isFiniteRelIndex_of_finiteIndex
    exact Subgroup.relIndex_ne_zero
  have hmn : m ≤ H.index :=
    Nat.le_of_dvd (by omega) (H.relIndex_dvd_index_of_le K.2)
  have hrle : Nat.log q m ≤ Nat.log q H.index := Nat.log_mono_right hmn
  refine ⟨⟨Nat.log q m, Nat.lt_succ_of_le hrle⟩, ?_, ?_⟩
  · exact ⟨Nat.pow_log_le_self q hm0, Nat.lt_pow_succ_log_self hq m⟩
  · intro r hr
    apply Fin.ext
    exact (Nat.log_eq_of_pow_le_of_lt_pow hr.1 hr.2).symm
end SharpIntermediateSubgroupBounds
