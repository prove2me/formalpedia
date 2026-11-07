-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_mem_lattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:32:17.905734+00:00
-- url     : https://prove2.me/submissions/240249bc-417b-4cec-8cba-d87ebafee73d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (hbound : bound ≤ r.matrixRank)
    (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ ∈
      InfinityCyclicLattice P r := by
  rw [infinityConjugationCorrectionSum]
  apply Submodule.sum_mem
  intro i hi
  have hiBound : i < bound := Finset.mem_range.mp hi
  exact cyclicMonomial_mem_infinityCyclicLattice P r _ i
    (lt_of_lt_of_le hiBound hbound)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
