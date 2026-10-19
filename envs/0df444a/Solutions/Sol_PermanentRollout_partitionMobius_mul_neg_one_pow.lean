-- Prove2me | solution 1 for PermanentRollout.partitionMobius_mul_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/b396c847-d4e4-4786-8455-ad2ec8a240f4

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {t : ℕ} {rows : Finset (Fin t)}
    (partition : Finpartition rows) :
    partitionMobius partition * (-1 : ℂ) ^ partition.parts.card =
      (-1 : ℂ) ^ rows.card *
        ∏ block ∈ partition.parts, ((block.card - 1).factorial : ℂ) := by
  classical
  calc
    partitionMobius partition * (-1 : ℂ) ^ partition.parts.card =
        (∏ block ∈ partition.parts,
          (-1 : ℂ) ^ (block.card - 1) * ((block.card - 1).factorial : ℂ)) *
          ∏ _block ∈ partition.parts, (-1 : ℂ) := by
      simp [partitionMobius]
    _ = ∏ block ∈ partition.parts,
          ((-1 : ℂ) ^ (block.card - 1) * ((block.card - 1).factorial : ℂ)) * -1 :=
      Finset.prod_mul_distrib.symm
    _ = ∏ block ∈ partition.parts,
          (-1 : ℂ) ^ block.card * ((block.card - 1).factorial : ℂ) := by
      apply Finset.prod_congr rfl
      intro block hblock
      have hcard : 0 < block.card :=
        Finset.card_pos.mpr (partition.nonempty_of_mem_parts hblock)
      have hsucc : block.card - 1 + 1 = block.card :=
        Nat.sub_add_cancel hcard
      have hpow : (-1 : ℂ) ^ block.card = (-1 : ℂ) ^ (block.card - 1) * -1 := by
        conv_lhs => rw [← hsucc, pow_succ]
      rw [hpow]
      ac_rfl
    _ = (-1 : ℂ) ^ (∑ block ∈ partition.parts, block.card) *
          ∏ block ∈ partition.parts, ((block.card - 1).factorial : ℂ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ = (-1 : ℂ) ^ rows.card *
          ∏ block ∈ partition.parts, ((block.card - 1).factorial : ℂ) := by
      rw [partition.sum_card_parts]
end PermanentRollout
