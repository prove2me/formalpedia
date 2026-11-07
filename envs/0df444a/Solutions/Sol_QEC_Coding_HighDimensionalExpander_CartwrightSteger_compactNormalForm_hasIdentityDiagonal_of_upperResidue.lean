-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactNormalForm_hasIdentityDiagonal_of_upperResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:39:14.825814+00:00
-- url     : https://prove2.me/submissions/40fd64bf-46c1-4612-a6f4-b4329cb0edd8

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constant_eq_zero_of_cyclicMonomial_mem_filtration_sup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalCompactNormalForm_conj_cyclicMonomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j : ℕ)
    (hupper : HasUpperUnipotentInfinityResidue P r
      (globalCompactNormalForm P r u j)) :
    CompactNormalFormHasIdentityDiagonal P r u j := by
  intro k
  apply LinearMap.ext
  intro c
  change compactConjugationDiagonalBlock P r u j k c = c
  have hdev := hupper.2 k c
  rw [globalCompactNormalForm_conj_cyclicMonomial P r u j c (k : ℕ)] at hdev
  have hmem : constantMatrix P r
        (compactConjugationDiagonalBlock P r u j k c - c) *
      cyclicGeneratorMatrix P r ^ (k : ℕ) ∈
        InfinityCyclicFiltration P r (k : ℕ) ⊔
          InfinityUniformizerMultiple P r := by
    convert hdev using 1
    rw [← sub_mul]
    change constantMatrixEmbedding P r
        (compactConjugationDiagonalBlock P r u j k c - c) * _ =
      (constantMatrixEmbedding P r
          (compactConjugationDiagonalBlock P r u j k c) -
        constantMatrixEmbedding P r c) * _
    rw [map_sub]
  exact sub_eq_zero.mp
    (constant_eq_zero_of_cyclicMonomial_mem_filtration_sup P r
      (compactConjugationDiagonalBlock P r u j k c - c) k hmem)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
