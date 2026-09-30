-- Prove2me | solution 1 for Rat.fractionalIdeal_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:04:09.842639+00:00
-- url     : https://prove2.me/submissions/23f9bd39-e13b-4c99-8b69-696b10139a2d

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup.Basic
open NumberField nonZeroDivisors
set_option autoImplicit false
theorem solution
    (I : (FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ)ˣ) :
    ((I : FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ) :
      Submodule (NumberField.RingOfIntegers ℚ) ℚ).IsPrincipal := by
  letI : IsPrincipalIdealRing (NumberField.RingOfIntegers ℚ) :=
    IsPrincipalIdealRing.of_surjective Rat.ringOfIntegersEquiv.symm
      Rat.ringOfIntegersEquiv.symm.surjective
  infer_instance
