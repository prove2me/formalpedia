-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:02.900287+00:00
-- url     : https://prove2.me/submissions/9db65dd6-aca9-45fd-aec0-78300b1673e3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution (P : GlobalPlace k F)
    (f : P.valuationRing) (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P (f • omega) =
      P.residue f * simplePoleResidue (k := k) (F := F) P omega := by
  rw [map_smul, Algebra.smul_def,
    IsLocalRing.ResidueField.algebraMap_eq]
  rfl
end QEC.Coding.AlgebraicGeometry.Differential
