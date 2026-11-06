-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:32:22.79275+00:00
-- url     : https://prove2.me/submissions/24c7914a-9c70-4d83-9146-36f5cd33e7d8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalUniformizerDerivative
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) (omega : simplePoleDifferentialLattice P)
    (homega : (omega : Differential k F) ∈ localDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P omega = 0 := by
  have homega' : omega ∈ regularDifferentialSubmoduleOfSimplePole P := homega
  rw [simplePoleResidue, LinearMap.comp_apply]
  rw [Submodule.mkQ_apply]
  rw [(Submodule.Quotient.mk_eq_zero
    (p := regularDifferentialSubmoduleOfSimplePole P) (x := omega)).mpr homega',
    map_zero]
end QEC.Coding.AlgebraicGeometry.Differential
