-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialToProjective_eq_one_of_fixed_projective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:46:09.287002+00:00
-- url     : https://prove2.me/submissions/ce34bdbb-2a5b-4931-af29-b99c56e78003

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_specialLinear_fixed_projective_is_homothety
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CongruenceLifting_residueTransvectionSpecial_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Matrix
open scoped commutatorElement
open scoped Pointwise
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (s : Matrix.SpecialLinearGroup (Fin r.matrixRank)
      (ResidueField P r level))
    (hfix : ∀ x : ℙ (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level), s • x = x) :
    specialToProjective P r level s = 1 := by
  let a : SpecialLinearGroup (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level) :=
    Matrix.SpecialLinearGroup.toLin'_equiv s
  have hfixa : ∀ x : ℙ (ResidueField P r level)
      (Fin r.matrixRank → ResidueField P r level), a • x = x := by
    intro x
    exact hfix x
  obtain ⟨c, hc⟩ := specialLinear_fixed_projective_is_homothety a hfixa
  rw [specialToProjective]
  change Matrix.ProjGenLinGroup.mk
    (Matrix.SpecialLinearGroup.toGL s) = 1
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  calc
    Matrix.toLin' (Matrix.scalar (Fin r.matrixRank) c) = c • 1 := by
      ext v i
      by_cases h : v = i <;>
        simp [Matrix.scalar, Matrix.toLin'_apply', Pi.single_apply, h]
    _ = a.val.toLinearMap := hc.symm
    _ = Matrix.toLin' (Matrix.SpecialLinearGroup.toGL s :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) := by
      exact Matrix.SpecialLinearGroup.toLin'_to_linearMap s
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
