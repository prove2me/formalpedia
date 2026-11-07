-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.specialTransvection_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:44:27.734693+00:00
-- url     : https://prove2.me/submissions/d01b25ca-1b74-4c69-aa98-0961fb8297d1

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.GroupTheory.GroupAction.Iwasawa
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Independence
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
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
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]
    (i j k : n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (c : K) :
    ⁅specialTransvection i k hik c,
        specialTransvection k j hkj 1⁆ =
      specialTransvection i j hij c := by
  let A := specialTransvection i k hik c
  let B := specialTransvection k j hkj (1 : K)
  have hAinv : A⁻¹ = specialTransvection i k hik (-c) := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    rw [show (specialTransvection i k hik (-c) * A :
        Matrix.SpecialLinearGroup n K) =
      specialTransvection i k hik ((-c) + c) by
        apply Subtype.ext
        exact Matrix.transvection_mul_transvection_same
          (i := i) (j := k) hik (-c) c]
    simp [specialTransvection]
  have hBinv : B⁻¹ = specialTransvection k j hkj (-1 : K) := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    rw [show (specialTransvection k j hkj (-1 : K) * B :
        Matrix.SpecialLinearGroup n K) =
      specialTransvection k j hkj ((-1 : K) + 1) by
        apply Subtype.ext
        exact Matrix.transvection_mul_transvection_same
          (i := k) (j := j) hkj (-1) 1]
    simp [specialTransvection]
  change A * B * A⁻¹ * B⁻¹ = specialTransvection i j hij c
  rw [hAinv, hBinv]
  apply Subtype.ext
  let X : Matrix n n K := Matrix.single i k c
  let Y : Matrix n n K := Matrix.single k j 1
  have hXX : X * X = 0 := by
    dsimp [X]
    exact Matrix.single_mul_single_of_ne
      (c := c) i k i hik.symm c
  have hYY : Y * Y = 0 := by
    dsimp [Y]
    exact Matrix.single_mul_single_of_ne
      (c := (1 : K)) k j k hkj.symm 1
  have hYX : Y * X = 0 := by
    dsimp [X, Y]
    exact Matrix.single_mul_single_of_ne
      (c := (1 : K)) k j i hij.symm c
  have hXY : X * Y = Matrix.single i j c := by
    dsimp [X, Y]
    simpa using Matrix.single_mul_single_same
      (c := c) i k j (1 : K)
  have hnegX : Matrix.single i k (-c) = -X := by
    ext a b
    by_cases h : i = a ∧ k = b <;> simp [X, Matrix.single, h]
  have hnegY : Matrix.single k j (-1 : K) = -Y := by
    ext a b
    by_cases h : k = a ∧ j = b <;> simp [Y, Matrix.single, h]
  change (1 + Matrix.single i k c) * (1 + Matrix.single k j (1 : K)) *
    (1 + Matrix.single i k (-c)) * (1 + Matrix.single k j (-1 : K)) =
      1 + Matrix.single i j c
  rw [hnegX, hnegY]
  rw [show Matrix.single i k c = X by rfl,
    show Matrix.single k j (1 : K) = Y by rfl]
  rw [← hXY]
  noncomm_ring [hXX, hYY, hYX]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
