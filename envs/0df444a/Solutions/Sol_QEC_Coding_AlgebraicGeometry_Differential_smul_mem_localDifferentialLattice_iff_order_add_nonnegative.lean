-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.smul_mem_localDifferentialLattice_iff_order_add_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:34:42.204719+00:00
-- url     : https://prove2.me/submissions/6d6c44bb-1bcc-4f8f-bf7f-bddb04bebe84

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_LocalDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_localDifferentialLattice_iff_differentialOrder_nonnegative


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
    (P : GlobalPlace k F) (f : F) (hf : f ≠ 0)
    (omega : Differential k F) (homega : omega ≠ 0) :
    f • omega ∈ localDifferentialLattice P ↔
      0 ≤ P.order f + differentialOrder (k := k) (F := F) P omega homega := by
  rw [mem_localDifferentialLattice_iff_differentialOrder_nonnegative
    (k := k) (F := F) P (f • omega) (smul_ne_zero hf homega)]
  rw [differentialOrder_smul (k := k) (F := F) P f hf omega homega]
end QEC.Coding.AlgebraicGeometry.Differential
