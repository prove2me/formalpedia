-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_prime_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:15.434648+00:00
-- url     : https://prove2.me/submissions/3c4530cc-2c10-4f14-ad89-f6b077f9d116

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_base_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_prime
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
theorem _root_.solution (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Function.Injective (fun t : constantTorus f epsilon y =>
      (t : ProjectiveGroup (f epsilon) y) *
        projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne *
          (t : ProjectiveGroup (f epsilon) y)⁻¹) := by
  intro t u hEqual
  dsimp only at hEqual
  rw [constantTorus_conjugate_prime f epsilon y hEpsilon hY hOne t,
    constantTorus_conjugate_prime f epsilon y hEpsilon hY hOne u] at hEqual
  exact constantTorus_conjugate_base_injective f epsilon y hEpsilon hY hOne hTwo
    (mul_left_cancel hEqual)
end QEC.Coding.ExpanderCodes.QuaternionGenerators
