-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.constantProjectiveMap_eq_one_of_commutes_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:30.355269+00:00
-- url     : https://prove2.me/submissions/9bd86883-5eba-47ba-93ea-fba84dc1c224

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_eq_scalar_of_mem_center
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
theorem _root_.solution
    (f : F →+* K) (epsilon : F) (y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0)
    (a : (QuadraticAlgebra F epsilon 0)ˣ)
    (hCommute : constantProjectiveMap f epsilon y a * projectiveBase (f epsilon) y hY hOne =
      projectiveBase (f epsilon) y hY hOne * constantProjectiveMap f epsilon y a) :
    constantProjectiveMap f epsilon y a = 1 := by
  let image := Units.map (coefficientEmbedding f epsilon y).toMonoidHom a
  let b := baseUnit (f epsilon) y hY hOne
  let c := (image * b) / (b * image)
  have hCenter : c ∈ Subgroup.center (Model (f epsilon) y)ˣ := by
    apply QuotientGroup.eq_iff_div_mem.mp
    simpa [constantProjectiveMap, projectiveBase, image, b, QuotientGroup.mk_mul]
      using hCommute
  have hScalar := val_eq_scalar_of_mem_center (f epsilon) y ((map_ne_zero f).mpr hEpsilon)
    hOne hTwo c hCenter
  have hProduct : image * b = c * (b * image) := by simp [c]
  have hValue := congrArg (fun u : (Model (f epsilon) y)ˣ => (u : Model (f epsilon) y))
    hProduct
  simp only [Units.val_mul] at hValue
  rw [hScalar] at hValue
  have hRe := congrArg QuaternionAlgebra.re hValue
  have hImI := congrArg QuaternionAlgebra.imI hValue
  simp [image, b, coefficientEmbedding, base] at hRe hImI
  have hScale : (c : Model (f epsilon) y).re = 1 := by
    by_cases hReal : f (a : QuadraticAlgebra F epsilon 0).re = 0
    · have hImag : f (a : QuadraticAlgebra F epsilon 0).im ≠ 0 := by
        intro hImag
        have hRealF : (a : QuadraticAlgebra F epsilon 0).re = 0 :=
          f.injective (by simpa using hReal)
        have hImagF : (a : QuadraticAlgebra F epsilon 0).im = 0 :=
          f.injective (by simpa using hImag)
        have hInverse := congrArg QuadraticAlgebra.re a.val_inv
        have hZeroOne : (0 : F) = 1 := by
          simpa only [QuadraticAlgebra.re_mul, hRealF, hImagF, zero_mul, mul_zero,
            add_zero, QuadraticAlgebra.re_one] using hInverse
        exact zero_ne_one hZeroOne
      apply mul_right_cancel₀ hImag
      simpa using hImI.symm
    · apply mul_right_cancel₀ hReal
      simpa using hRe.symm
  have hK := congrArg QuaternionAlgebra.imK hValue
  simp [image, b, coefficientEmbedding, base, hScale] at hK
  field_simp at hK
  have hDouble : (2 : K) * f (a : QuadraticAlgebra F epsilon 0).im = 0 := by
    linear_combination -hK
  apply (constantProjectiveMap_eq_one_iff f epsilon y hOne hTwo a).mpr
  exact f.injective (by simpa using (mul_eq_zero.mp hDouble).resolve_left hTwo)
end QEC.Coding.ExpanderCodes.QuaternionGenerators
