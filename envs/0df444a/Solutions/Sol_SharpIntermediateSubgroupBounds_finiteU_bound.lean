-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.finiteU_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:26.688555+00:00
-- url     : https://prove2.me/submissions/66dca1d2-89f0-460a-95be-c697be15523c

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_band_card_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_intervalToBandSigma_injective

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) :
    (Nat.card (interval H) : ℚ) ≤ finiteUQ H.index q := by
  have hcardNat : Fintype.card (interval H) ≤
      Fintype.card (Σ r : Fin (Nat.log q H.index + 1), band H q r.1) :=
    Fintype.card_le_of_injective (intervalToBandSigma H q hn hq)
      (intervalToBandSigma_injective H q hn hq)
  have hcard : (Nat.card (interval H) : ℚ) ≤
      ∑ r : Fin (Nat.log q H.index + 1),
        (Nat.card (band H q (r : ℕ)) : ℚ) := by
    rw [Nat.card_eq_fintype_card]
    simp_rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_sigma] at hcardNat
    exact_mod_cast hcardNat
  calc
    (Nat.card (interval H) : ℚ) ≤
        ∑ r : Fin (Nat.log q H.index + 1),
          (Nat.card (band H q (r : ℕ)) : ℚ) := hcard
    _ ≤ ∑ r : Fin (Nat.log q H.index + 1),
        (H.index : ℚ) ^ (r : ℕ) /
          (gammaQ q (r : ℕ) *
            (q : ℚ) ^ ((r : ℕ) * (r : ℕ))) :=
      Finset.sum_le_sum fun r _ => band_card_bound hn hq hqp (r : ℕ)
    _ = finiteUQ H.index q := rfl
end SharpIntermediateSubgroupBounds
