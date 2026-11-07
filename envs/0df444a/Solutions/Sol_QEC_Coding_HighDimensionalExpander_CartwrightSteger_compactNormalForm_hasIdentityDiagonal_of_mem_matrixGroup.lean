-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactNormalForm_hasIdentityDiagonal_of_mem_matrixGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:49.980337+00:00
-- url     : https://prove2.me/submissions/ccfbefc8-2bc6-4e9e-a38d-82b898324566

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_compactNormalForm_hasIdentityDiagonal_of_upperResidue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j : ℕ)
    (hmem : globalCompactNormalForm P r u j ∈
      CartwrightStegerMatrixGroup P r) :
    CompactNormalFormHasIdentityDiagonal P r u j := by
  apply compactNormalForm_hasIdentityDiagonal_of_upperResidue P r u j
  exact cartwrightStegerMatrixGroup_le_upperUnipotentInfinityResidueSubgroup
    P r hmem
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
