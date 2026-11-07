-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityConjugationCorrectionSum_mem_filtration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:35:32.053193+00:00
-- url     : https://prove2.me/submissions/faba15a4-dd39-4f56-8ad0-2c5d31f4db8d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicMonomial_mem_infinityCyclicFiltration

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (k bound : ℕ) (hbound : bound ≤ r.matrixRank)
    (ζ : ConstantExtension P r) :
    infinityConjugationCorrectionSum P r u k bound ζ ∈
      InfinityCyclicFiltration P r bound := by
  rw [infinityConjugationCorrectionSum]
  apply Submodule.sum_mem
  intro i hi
  have hiBound : i < bound := Finset.mem_range.mp hi
  exact cyclicMonomial_mem_infinityCyclicFiltration P r bound _ i hiBound
    (lt_of_lt_of_le hiBound hbound)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
