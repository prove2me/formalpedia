-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:04.073703+00:00
-- url     : https://prove2.me/submissions/c1ae01ef-f6ba-41fb-808a-087944f680b3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleTraceResidue_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_apply


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution :
    globalSimplePoleResidue (k := k) (F := F) 0
      (isGlobalSimplePole_zero (k := k) (F := F)) = 0 := by
  ext P
  rw [globalSimplePoleResidue_apply]
  exact simplePoleTraceResidue_zero (k := k) (F := F) P
end QEC.Coding.AlgebraicGeometry.Differential
