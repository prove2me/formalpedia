-- Prove2me | solution 1 for SIBrochure.second_from_defining_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T22:38:53.235291+00:00
-- url     : https://prove2.me/submissions/2ed8bab6-315a-492d-bed8-72be304c8141

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution :
    hertz = (1 / 9192631770 : ℝ) • deltaNuCs ∧
    second = (9192631770 : ℝ) • deltaNuCs⁻¹ := by
  refine ⟨?_, ?_⟩ <;>
  · ext <;> simp [hertz, deltaNuCs, second, base, unitOf]
