-- Prove2me | solution 1 for SIBrochure.candela_from_defining_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T22:53:24.580811+00:00
-- url     : https://prove2.me/submissions/1367653b-3440-4abb-bf64-7f2c13b970e3

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution :
    candela = (1 / 683 : ℝ) •
      (Kcd * kilogram * metre ^ (2 : ℤ) * second ^ (-3 : ℤ) * steradian⁻¹) ∧
    candela = (1 / (6.62607015e-34 * (9192631770 : ℝ) ^ 2 * 683)) •
      (deltaNuCs ^ (2 : ℤ) * h * Kcd) := by
  refine ⟨?_, ?_⟩ <;>
  · ext <;>
      simp [hertz, deltaNuCs, h, Kcd, lumen, watt, steradian, joule, candela, kilogram, metre,
        second, base, unitOf] <;>
      first | ring1 | norm_num
