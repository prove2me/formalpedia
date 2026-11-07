-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.sum_mul_cyclicGeneratorMatrix_pow_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:19:40.175884+00:00
-- url     : https://prove2.me/submissions/872f53a3-a7c1-4a86-beea-f2b75037c93f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicGeneratorMatrix_pow_rank_add

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (k : ℕ) (hk : k ≤ r.matrixRank)
    (A : ℕ → Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r)) :
    ∑ i ∈ Finset.range r.matrixRank,
        A i * cyclicGeneratorMatrix P r ^ (k + i) =
      (∑ i ∈ Finset.range (r.matrixRank - k),
        A i * cyclicGeneratorMatrix P r ^ (k + i)) +
      (onePlusY P r) •
        ∑ j ∈ Finset.range k,
          A (r.matrixRank - k + j) * cyclicGeneratorMatrix P r ^ j := by
  have hrank : r.matrixRank - k + k = r.matrixRank :=
    Nat.sub_add_cancel hk
  have hrange :
      Finset.range r.matrixRank = Finset.range (r.matrixRank - k + k) :=
    congrArg Finset.range hrank.symm
  rw [hrange, Finset.sum_range_add]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hexponent : k + (r.matrixRank - k + j) = r.matrixRank + j := by
    omega
  rw [hexponent, cyclicGeneratorMatrix_pow_rank_add]
  exact mul_smul_comm (onePlusY P r) (A (r.matrixRank - k + j))
    (cyclicGeneratorMatrix P r ^ j)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
