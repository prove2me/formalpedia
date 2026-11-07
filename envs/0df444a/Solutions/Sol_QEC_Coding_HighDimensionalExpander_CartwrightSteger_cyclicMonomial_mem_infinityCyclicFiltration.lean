-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicMonomial_mem_infinityCyclicFiltration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:33:39.026316+00:00
-- url     : https://prove2.me/submissions/181c3c95-f4f6-4bb6-b6a1-c30384c5e8a1

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
    (P : BasePrime) (r : Rank) (bound : ℕ)
    (c : ConstantExtension P r) (k : ℕ)
    (hkBound : k < bound) (hkRank : k < r.matrixRank) :
    constantMatrix P r c * cyclicGeneratorMatrix P r ^ k ∈
      InfinityCyclicFiltration P r bound :=
  Submodule.subset_span ⟨c, k, hkBound, hkRank, rfl⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
