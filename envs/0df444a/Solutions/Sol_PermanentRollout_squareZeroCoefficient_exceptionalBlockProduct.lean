-- Prove2me | solution 1 for PermanentRollout.squareZeroCoefficient_exceptionalBlockProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/c140248a-de9a-4c51-a46d-16870c8a29b2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_variable_product_mul
import Theorems.Thm_PermanentRollout_squareZeroCoefficient_squareZeroBlockSum_pow
import Theorems.Thm_PermanentRollout_squareZero_fullBlockProduct

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {r : ℕ} {ι : Type*}
    (blocks : ι → Finset (Fin r)) (indices : Finset ι)
    (exceptional : ι) (t d : ℕ)
    (target : Finset (Fin r))
    (hcard : ∀ i ∈ indices, (blocks i).card = t)
    (hdisjoint : Set.PairwiseDisjoint (↑indices) blocks) :
    squareZeroCoefficient r target
      (squareZeroBlockSum r (blocks exceptional) ^ (t - d) *
        ∏ i ∈ indices, squareZeroBlockSum r (blocks i) ^ t) =
      if indices.biUnion blocks ⊆ target ∧
          target \ indices.biUnion blocks ⊆ blocks exceptional ∧
          (target \ indices.biUnion blocks).card = t - d then
        ((t.factorial ^ indices.card : ℕ) : ℂ) *
          (((t - d).factorial : ℕ) : ℂ)
      else 0 := by
  classical
  rw [squareZero_fullBlockProduct blocks indices t hcard hdisjoint]
  have hscalar :
      squareZeroBlockSum r (blocks exceptional) ^ (t - d) *
          (((t.factorial ^ indices.card : ℕ) : SquareZeroAlgebra r) *
            ∏ row ∈ indices.biUnion blocks, squareZeroVariable r row) =
        ((t.factorial ^ indices.card : ℕ) : ℂ) •
          ((∏ row ∈ indices.biUnion blocks, squareZeroVariable r row) *
            squareZeroBlockSum r (blocks exceptional) ^ (t - d)) := by
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    ring
  rw [hscalar, map_smul,
    squareZeroCoefficient_variable_product_mul,
    squareZeroCoefficient_squareZeroBlockSum_pow]
  split_ifs <;> simp_all
end PermanentRollout
