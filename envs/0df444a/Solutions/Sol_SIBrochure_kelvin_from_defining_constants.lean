-- Prove2me | solution 1 for SIBrochure.kelvin_from_defining_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T22:50:13.533711+00:00
-- url     : https://prove2.me/submissions/3b0bc177-730b-45c4-aaed-76e2889e54e1

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution :
    kelvin = (1.380649e-23 : ℝ) •
      (k⁻¹ * kilogram * metre ^ (2 : ℤ) * second ^ (-2 : ℤ)) ∧
    kelvin = (1.380649e-23 / (6.62607015e-34 * 9192631770) : ℝ) •
      (deltaNuCs * h / k) := by
  refine ⟨?_, ?_⟩ <;>
  · ext <;>
      simp [hertz, deltaNuCs, h, k, joule, kelvin, kilogram, metre, second, base, unitOf] <;>
      first | ring1 | norm_num
