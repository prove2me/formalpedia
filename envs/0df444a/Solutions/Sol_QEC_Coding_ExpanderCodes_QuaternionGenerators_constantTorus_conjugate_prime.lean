-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:42.10444+00:00
-- url     : https://prove2.me/submissions/7ce46e63-4165-4d3d-8bb0-59a69d5e0859

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_eq_alpha_mul_base
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_commutes_alpha
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
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (t : constantTorus f epsilon y) :
    (t : ProjectiveGroup (f epsilon) y) *
        projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹ =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
        ((t : ProjectiveGroup (f epsilon) y) * projectiveBase (f epsilon) y hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹) := by
  rw [projectivePrime_eq_alpha_mul_base]
  calc
    _ = ((t : ProjectiveGroup (f epsilon) y) *
        projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon)) *
          projectiveBase (f epsilon) y hY hOne * (t : ProjectiveGroup (f epsilon) y)⁻¹ := by
      simp [mul_assoc]
    _ = _ := by
      rw [constantTorus_commutes_alpha f epsilon y hEpsilon t]
      simp [mul_assoc]
end QEC.Coding.ExpanderCodes.QuaternionGenerators
