-- Prove2me | solution 1 for SIBrochure.every_unit_from_defining_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T14:37:54.092982+00:00
-- url     : https://prove2.me/submissions/0f52a434-2006-4a2b-a0bb-eb4e86256a54

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution (u : BaseUnit → ℤ) :
    ∃ (a : ℝ) (n : DefiningConstant → ℤ),
      unitOf u = a • ∏ i : DefiningConstant, i.value ^ (n i) := by
  classical
  let n : DefiningConstant → ℤ := fun i => match i with
    | .deltaNuCs => -u .second - u .metre + u .kilogram + u .ampere + u .kelvin + 2 * u .candela
    | .c => u .metre - 2 * u .kilogram
    | .h => u .kilogram + u .kelvin + u .candela
    | .e => u .ampere
    | .k => -u .kelvin
    | .NA => -u .mole
    | .Kcd => u .candela
  have huniv : (Finset.univ : Finset DefiningConstant) =
      {.deltaNuCs, .c, .h, .e, .k, .NA, .Kcd} := rfl
  have hexp : (∏ i : DefiningConstant, i.value ^ (n i)).exp = u := by
    rw [huniv]
    funext b
    cases b <;>
    simp [Finset.prod_insert, DefiningConstant.value, n, hertz, deltaNuCs, h, c, e, k, NA, Kcd,
      joule, coulomb, watt, lumen, steradian, kilogram, metre, second, ampere, kelvin, mole,
      candela, base, unitOf] <;> ring
  have hnum : (∏ i : DefiningConstant, i.value ^ (n i)).num ≠ 0 := by
    rw [huniv]
    simp [Finset.prod_insert, DefiningConstant.value, hertz, deltaNuCs, h, c, e, k, NA, Kcd,
      joule, coulomb, watt, lumen, steradian, kilogram, metre, second, ampere, kelvin, mole,
      candela, base, unitOf]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact zpow_ne_zero _ (by norm_num)
  refine ⟨(∏ i : DefiningConstant, i.value ^ (n i)).num⁻¹, n, ?_⟩
  ext
  · simp only [Quantity.smul_num]
    rw [inv_mul_cancel₀ hnum]
    rfl
  · simp only [Quantity.smul_exp, hexp]
    rfl
