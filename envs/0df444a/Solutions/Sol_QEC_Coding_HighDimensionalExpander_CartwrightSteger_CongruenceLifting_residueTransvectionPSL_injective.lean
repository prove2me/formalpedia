-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionPSL_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:42:04.9037+00:00
-- url     : https://prove2.me/submissions/63b47c9c-cd61-4e82-b078-a6d87de1f346

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
section
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace CongruenceLifting
open Matrix
private theorem residueTransvectionSpecial_mul
    (P : BasePrime) (r : Rank) (level : Nat)
    (c d : ResidueField P r level) :
    residueTransvectionSpecial P r level c *
        residueTransvectionSpecial P r level d =
      residueTransvectionSpecial P r level (c + d) := by
  classical
  apply Subtype.ext
  exact Matrix.transvection_mul_transvection_same
    (i := rankFirstIndex r) (j := rankSecondIndex r)
    (rankFirstIndex_ne_rankSecondIndex r) c d
end CongruenceLifting
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (residueTransvectionPSL P r level) := by
  intro c d hcd
  have hprojective :
      specialToProjective P r level
          (residueTransvectionSpecial P r level c) =
        specialToProjective P r level
          (residueTransvectionSpecial P r level d) :=
    congrArg Subtype.val hcd
  have hmul :
      residueTransvectionSpecial P r level c *
          residueTransvectionSpecial P r level (d - c) =
        residueTransvectionSpecial P r level d := by
    rw [residueTransvectionSpecial_mul]
    congr 1
    abel
  have hprojective_zero :
      specialToProjective P r level
          (residueTransvectionSpecial P r level (d - c)) = 1 := by
    have hmapped := congrArg (specialToProjective P r level) hmul
    rw [map_mul, hprojective] at hmapped
    have hcancelled := congrArg
      (fun x =>
        ((specialToProjective P r level)
          (residueTransvectionSpecial P r level d))⁻¹ * x) hmapped
    simpa [mul_assoc] using hcancelled
  have hcenter :
      Matrix.SpecialLinearGroup.toGL
          (residueTransvectionSpecial P r level (d - c)) ∈
        Subgroup.center
          (Matrix.GeneralLinearGroup (Fin r.matrixRank)
            (ResidueField P r level)) := by
    apply Matrix.ProjGenLinGroup.mk_eq_one.mp
    simpa [specialToProjective] using hprojective_zero
  obtain ⟨a, ha⟩ :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hcenter
  have hoffdiag := congrArg
    (fun M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
        (ResidueField P r level) =>
      M (rankFirstIndex r) (rankSecondIndex r)) ha
  have hdc : 0 = d - c := by
    change (Matrix.scalar (Fin r.matrixRank) a)
        (rankFirstIndex r) (rankSecondIndex r) =
      Matrix.transvection (rankFirstIndex r) (rankSecondIndex r) (d - c)
        (rankFirstIndex r) (rankSecondIndex r) at hoffdiag
    simpa [residueTransvectionSpecial, Matrix.transvection,
      Matrix.scalar_apply, rankFirstIndex_ne_rankSecondIndex] using hoffdiag
  exact (sub_eq_zero.mp hdc.symm).symm
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
