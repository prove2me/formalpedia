-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_logarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:36:23.072124+00:00
-- url     : https://prove2.me/submissions/e5c8f268-aad5-4709-b21c-28c712418c27

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_SimplePoleResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_LogarithmicResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_localDifferentialLattice_le_simplePoleDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_uniformizerLogDifferential


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.Differential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0) :
    simplePoleResidue (k := k) (F := F) P
        (logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf) =
      (P.order f : GlobalPlace.residueField P) := by
  obtain ⟨u, hu⟩ := logarithmicDifferential_eq_unit_add_order_smul
    (k := k) (F := F) P f hf
  let unitLog : simplePoleDifferentialLattice P :=
    ⟨logarithmicDifferential (k := k) (F := F) (u : F),
      localDifferentialLattice_le_simplePoleDifferentialLattice
        (k := k) (F := F) P
        (logarithmicDifferential_mem_localDifferentialLattice_of_unit
          (k := k) (F := F) P u)⟩
  have hdecomposition :
      logarithmicDifferentialAtSimplePole (k := k) (F := F) P f hf =
        unitLog + P.order f • uniformizerLogDifferential (k := k) (F := F) P := by
    apply Subtype.ext
    exact hu
  rw [hdecomposition, map_add, map_zsmul,
    simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P unitLog,
    simplePoleResidue_uniformizerLogDifferential (k := k) (F := F) P,
    zero_add, zsmul_one]
  exact logarithmicDifferential_mem_localDifferentialLattice_of_unit
    (k := k) (F := F) P u
end QEC.Coding.AlgebraicGeometry.Differential
