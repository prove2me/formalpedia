-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.val_eq_scalar_of_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:34:40.168745+00:00
-- url     : https://prove2.me/submissions/be885d75-7704-4524-884a-793edd9431cd

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (Model epsilon y)ˣ) (ha : a ∈ Subgroup.center (Model epsilon y)ˣ) :
    (a : Model epsilon y) = (((a : Model epsilon y).re : K) : Model epsilon y) := by
  have hAlpha := Subgroup.mem_center_iff.mp ha (alphaUnit epsilon y hEpsilon)
  have hZ := Subgroup.mem_center_iff.mp ha (skewUnit epsilon y hOne)
  have hI := congrArg (fun b : (Model epsilon y)ˣ => (b : Model epsilon y).imK) hZ
  have hJ := congrArg (fun b : (Model epsilon y)ˣ => (b : Model epsilon y).imK) hAlpha
  have hK := congrArg (fun b : (Model epsilon y)ˣ => (b : Model epsilon y).imJ) hAlpha
  simp [skewUnit, z] at hI
  simp [alpha] at hJ hK
  have hDoubleI : (2 : K) * (a : Model epsilon y).imI = 0 := by
    linear_combination -hI
  have hDoubleJ : (2 : K) * (a : Model epsilon y).imJ = 0 := by
    linear_combination hJ
  have hDoubleK : (2 : K) * epsilon * (a : Model epsilon y).imK = 0 := by
    linear_combination hK
  have hImagI := (mul_eq_zero.mp hDoubleI).resolve_left hTwo
  have hImagJ := (mul_eq_zero.mp hDoubleJ).resolve_left hTwo
  have hImagK := (mul_eq_zero.mp hDoubleK).resolve_left (mul_ne_zero hTwo hEpsilon)
  ext <;> simp [hImagI, hImagJ, hImagK]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
