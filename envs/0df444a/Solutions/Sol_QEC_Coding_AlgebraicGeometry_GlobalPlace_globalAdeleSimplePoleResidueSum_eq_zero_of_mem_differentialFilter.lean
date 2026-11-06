-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_eq_zero_of_mem_differentialFilter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:22.000711+00:00
-- url     : https://prove2.me/submissions/a31ab256-f5fc-4154-a931-b79c77cd2ed3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialResidueAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleDifferentialResidueScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    (omega : Differential k F) (homega : omega ≠ 0)
    (a : globalAdeleFilter (k := k) (F := F)
      (FunctionFieldDifferential.differentialDivisor
        (k := k) (F := F) omega homega)) :
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
          (k := k) (F := F) omega homega a.property⟩ = 0 := by
  change (globalAdeleSimplePoleResidue (k := k) (F := F) omega homega
    ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
      (k := k) (F := F) omega homega a.property⟩).sum
      (fun _ residue => residue) = 0
  have hfamily : globalAdeleSimplePoleResidue
      (k := k) (F := F) omega homega
      ⟨a, globalAdeleFilter_le_globalAdeleSimplePoleSubmodule
        (k := k) (F := F) omega homega a.property⟩ = 0 := by
    ext P
    exact Differential.simplePoleTraceResidue_eq_zero_of_mem_localDifferentialLattice
      (k := k) (F := F) P _ _
        (globalAdeleFilter_product_mem_localDifferentialLattice
          (k := k) (F := F) omega homega a P)
  rw [hfamily]
  exact Finsupp.sum_zero_index
end QEC.Coding.AlgebraicGeometry.GlobalPlace
