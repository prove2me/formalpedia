-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:13.181128+00:00
-- url     : https://prove2.me/submissions/e3c93112-3c6d-414d-9e97-3e03f16a9051

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution :
    globalSimplePoleResidueSum (k := k) (F := F) 0
      (isGlobalSimplePole_zero (k := k) (F := F)) = 0 := by
  rw [globalSimplePoleResidueSum, globalSimplePoleResidue_zero]
  exact Finsupp.sum_zero_index
end QEC.Coding.AlgebraicGeometry.Differential
