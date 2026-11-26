-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.band_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:49.503643+00:00
-- url     : https://prove2.me/submissions/60fe0bef-4d3e-4da6-bd09-4934affc2123

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_bandwise_moment
import Theorems.Thm_SharpIntermediateSubgroupBounds_band_card_mul_pow_le_moment
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_pos


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
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    (Nat.card (band H q r) : ℚ) ≤
      (H.index : ℚ) ^ r /
        (gammaQ q r * (q : ℚ) ^ (r * r)) := by
  have hmass := band_card_mul_pow_le_moment H q r
  have hmoment := bandwise_moment hn hq hqp r
  have hgamma : 0 < gammaQ q r := gammaQ_pos hq
  have hqpow : (0 : ℚ) < (q : ℚ) ^ (r * r) := by positivity
  apply (le_div_iff₀ (mul_pos hgamma hqpow)).2
  calc
    (Nat.card (band H q r) : ℚ) *
          (gammaQ q r * (q : ℚ) ^ (r * r)) =
        gammaQ q r *
          ((Nat.card (band H q r) : ℚ) * (q : ℚ) ^ (r * r)) := by
      ring
    _ ≤ gammaQ q r *
          (∑ K : band H q r, (H.relIndex K.1 : ℚ) ^ r) := by
      apply mul_le_mul_of_nonneg_left _ hgamma.le
      exact_mod_cast hmass
    _ ≤ (H.index : ℚ) ^ r := hmoment
end SharpIntermediateSubgroupBounds
