-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_eq_residueCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:44:49.989784+00:00
-- url     : https://prove2.me/submissions/2ffb9e3e-037a-4533-99bd-372cb7984ac4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_uniformizerLogDifferential


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
    (omega : simplePoleDifferentialLattice P) :
    simplePoleResidue (k := k) (F := F) P omega =
      P.residue (simplePoleResidueCoordinate (k := k) (F := F) P omega) := by
  let r : P.valuationRing :=
    simplePoleResidueCoordinate (k := k) (F := F) P omega
  have homega : omega = r •
        uniformizerLogDifferential (k := k) (F := F) P := by
    apply Subtype.ext
    exact simplePoleDifferential_eq_residueCoordinate_smul_uniformizerLogDifferential
      (k := k) (F := F) P omega
  calc
    simplePoleResidue (k := k) (F := F) P omega =
        simplePoleResidue (k := k) (F := F) P
          (r • uniformizerLogDifferential (k := k) (F := F) P) :=
      congrArg (simplePoleResidue (k := k) (F := F) P) homega
    _ = P.residue r * simplePoleResidue (k := k) (F := F) P
        (uniformizerLogDifferential (k := k) (F := F) P) :=
      simplePoleResidue_smul (k := k) (F := F) P r
        (uniformizerLogDifferential (k := k) (F := F) P)
    _ = P.residue r := by
      rw [simplePoleResidue_uniformizerLogDifferential, mul_one]
    _ = P.residue
        (simplePoleResidueCoordinate (k := k) (F := F) P omega) := rfl
end QEC.Coding.AlgebraicGeometry.Differential
