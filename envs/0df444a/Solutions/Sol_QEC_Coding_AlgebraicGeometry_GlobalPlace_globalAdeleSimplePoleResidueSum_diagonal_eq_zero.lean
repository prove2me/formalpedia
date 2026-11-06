-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSimplePoleResidueSum_diagonal_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:22.837595+00:00
-- url     : https://prove2.me/submissions/7806c9e6-58c5-4d7c-8b89-c91985b29912

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleWeilDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleDifferentialResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_eq_zero


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
    (omega : Differential k F) (homega : omega ≠ 0) (f : F)
    (hf : diagonalAdele (k := k) (F := F) f ∈
      globalAdeleSimplePoleSubmodule (k := k) (F := F) omega) :
    globalAdeleSimplePoleResidueSum (k := k) (F := F) omega homega
        ⟨diagonalAdele (k := k) (F := F) f, hf⟩ = 0 := by
  let hglobal : Differential.IsGlobalSimplePole
      (k := k) (F := F) (f • omega) := fun P => by
    exact hf P
  have hfamily : globalAdeleSimplePoleResidue
      (k := k) (F := F) omega homega
      ⟨diagonalAdele (k := k) (F := F) f, hf⟩ =
        Differential.globalSimplePoleResidue
          (k := k) (F := F) (f • omega) hglobal := by
    ext P
    rfl
  change (globalAdeleSimplePoleResidue (k := k) (F := F) omega homega
    ⟨diagonalAdele (k := k) (F := F) f, hf⟩).sum
      (fun _ residue => residue) = 0
  rw [hfamily]
  exact Differential.globalSimplePoleResidueSum_eq_zero
    (k := k) (F := F) (f • omega) hglobal
end QEC.Coding.AlgebraicGeometry.GlobalPlace
