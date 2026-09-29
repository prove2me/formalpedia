-- Prove2me | solution 1 for SIBrochure.metre_from_defining_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T22:38:53.069995+00:00
-- url     : https://prove2.me/submissions/382a190c-e6a2-4438-8945-4d87a8f1e402

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution :
    metre = (1 / 299792458 : ℝ) • (c * second) ∧
    metre = (9192631770 / 299792458 : ℝ) • (c / deltaNuCs) := by
  refine ⟨?_, ?_⟩ <;>
  · ext <;> simp [hertz, deltaNuCs, c, metre, second, base, unitOf]
