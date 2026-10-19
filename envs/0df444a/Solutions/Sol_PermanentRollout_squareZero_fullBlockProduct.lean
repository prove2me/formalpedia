-- Prove2me | solution 1 for PermanentRollout.squareZero_fullBlockProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/15266dbc-99df-47b8-8eb3-a7e9a9662dd3

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZeroBlockSum_pow_card

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ} {ι : Type*}
    (blocks : ι → Finset (Fin r))
    (indices : Finset ι) (t : ℕ)
    (hcard : ∀ i ∈ indices, (blocks i).card = t)
    (hdisjoint : Set.PairwiseDisjoint (↑indices) blocks) :
    (∏ i ∈ indices, squareZeroBlockSum r (blocks i) ^ t) =
      ((t.factorial ^ indices.card : ℕ) : SquareZeroAlgebra r) *
        ∏ row ∈ indices.biUnion blocks, squareZeroVariable r row := by
  classical
  calc
    (∏ i ∈ indices, squareZeroBlockSum r (blocks i) ^ t) =
        ∏ i ∈ indices,
          ((t.factorial : ℕ) : SquareZeroAlgebra r) *
            ∏ row ∈ blocks i, squareZeroVariable r row := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [← hcard i hi, squareZeroBlockSum_pow_card]
    _ = ((t.factorial : ℕ) : SquareZeroAlgebra r) ^ indices.card *
          ∏ i ∈ indices,
            ∏ row ∈ blocks i, squareZeroVariable r row := by
              rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = ((t.factorial ^ indices.card : ℕ) : SquareZeroAlgebra r) *
          ∏ row ∈ indices.biUnion blocks, squareZeroVariable r row := by
              rw [Nat.cast_pow, Finset.prod_biUnion hdisjoint]
end PermanentRollout
