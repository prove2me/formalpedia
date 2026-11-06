-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleTraceResidue_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:38:02.092217+00:00
-- url     : https://prove2.me/submissions/09037e94-487b-4c53-998c-9ba954871dbc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidueLinear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (P : GlobalPlace k F) :
    simplePoleTraceResidue (k := k) (F := F) P 0
      (simplePoleDifferentialLattice P).zero_mem = 0 := by
  exact simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := F) P 0 (simplePoleDifferentialLattice P).zero_mem
      (localDifferentialLattice P).zero_mem
end QEC.Coding.AlgebraicGeometry.Differential
