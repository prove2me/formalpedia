-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:47:38.232977+00:00
-- url     : https://prove2.me/submissions/65c4de86-fac8-4c08-8587-103dfb9fdd9b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerGenerator_mem_upperUnipotentInfinityResidueSubgroup

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    CartwrightStegerMatrixGroup P r ≤
      UpperUnipotentInfinityResidueSubgroup P r := by
  rw [CartwrightStegerMatrixGroup]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨x, rfl⟩
  exact cartwrightStegerGenerator_mem_upperUnipotentInfinityResidueSubgroup
    P r x
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
