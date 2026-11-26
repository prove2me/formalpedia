-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.totalQBinom_odd_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:22.83414+00:00
-- url     : https://prove2.me/submissions/3f4dc179-d2c4-4e25-ab2b-7a9311dec1f6

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_qBinom_symm


set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q) (a : ℕ) :
    totalQBinom q (2 * a + 1) =
      2 * ∑ j ∈ Finset.range (a + 1), qBinom q (2 * a + 1) (a + 1 + j) := by
  let f : ℕ → ℕ := fun k ↦ qBinom q (2 * a + 1) k
  have hlow : (∑ j ∈ Finset.range (a + 1), f j) =
      ∑ j ∈ Finset.range (a + 1), f (a + 1 + j) := by
    calc
      (∑ j ∈ Finset.range (a + 1), f j) =
          ∑ j ∈ Finset.range (a + 1), f (a + 1 - 1 - j) :=
        (Finset.sum_range_reflect f (a + 1)).symm
      _ = ∑ j ∈ Finset.range (a + 1), f (a + 1 + j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hja : j < a + 1 := Finset.mem_range.mp hj
        dsimp [f]
        rw [qBinom_symm hq (by omega : a - j ≤ 2 * a + 1)]
        congr 1
        omega
  rw [totalQBinom, Fin.sum_univ_eq_sum_range]
  have hsize : 2 * a + 1 + 1 = (a + 1) + (a + 1) := by omega
  rw [hsize, Finset.sum_range_add, hlow]
  dsimp [f]
  ring
end SharpIntermediateSubgroupBounds
