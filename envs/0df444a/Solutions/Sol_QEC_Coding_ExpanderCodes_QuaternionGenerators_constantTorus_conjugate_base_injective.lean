-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantTorus_conjugate_base_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:36:13.23363+00:00
-- url     : https://prove2.me/submissions/e29df455-3d3c-456f-86ca-e8ef887bbbcd

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantProjectiveMap_eq_one_of_commutes_base
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
      (t : ProjectiveGroup (f epsilon) y) * projectiveBase (f epsilon) y hY hOne *
        (t : ProjectiveGroup (f epsilon) y)⁻¹) := by
  intro t u hEqual
  have hCommute := congrArg (fun x => (u : ProjectiveGroup (f epsilon) y)⁻¹ * x *
    (t : ProjectiveGroup (f epsilon) y)) hEqual
  simp [mul_assoc] at hCommute
  have hMember : (u : ProjectiveGroup (f epsilon) y)⁻¹ * t ∈ constantTorus f epsilon y :=
    (constantTorus f epsilon y).mul_mem
      ((constantTorus f epsilon y).inv_mem u.property) t.property
  obtain ⟨a, ha⟩ := hMember
  have hIdentity := constantProjectiveMap_eq_one_of_commutes_base f epsilon y hEpsilon
    hY hOne hTwo a (by simpa [ha, mul_assoc] using hCommute)
  rw [ha] at hIdentity
  apply Subtype.ext
  exact (inv_mul_eq_one.mp hIdentity).symm
end QEC.Coding.ExpanderCodes.QuaternionGenerators
