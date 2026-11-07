-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerGenerator_mem_infinityLatticePreserverMonoid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:47.883873+00:00
-- url     : https://prove2.me/submissions/2dc3c04c-620c-4103-bcf0-a23fccc37d30

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_preservesInfinityCyclicLattice

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : ConstantProjectiveClass P r) :
    cartwrightStegerGenerator P r x ∈
      InfinityLatticePreserverMonoid P r :=
  cartwrightStegerGenerator_preservesInfinityCyclicLattice P r x
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
