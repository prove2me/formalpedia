-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.localDifferentialLattice_le_simplePoleDifferentialLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:20:29.653451+00:00
-- url     : https://prove2.me/submissions/992f42eb-e2b8-4a23-b7fa-d56a783d3332

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_GlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalPlace
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped WithZero
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
open QEC.Coding.AlgebraicGeometry.Differential
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) :
    localDifferentialLattice P ≤ simplePoleDifferentialLattice P := by
  intro omega homega
  change P.uniformizerInValuationRing • omega ∈ localDifferentialLattice P
  exact (localDifferentialLattice P).smul_mem _ homega
end QEC.Coding.AlgebraicGeometry.Differential
