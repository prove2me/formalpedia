-- Prove2me | solution 1 for SIBrochure.mole_from_defining_constants
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T22:42:30.586545+00:00
-- url     : https://prove2.me/submissions/9d3b5ba7-392c-4b62-98cc-184a83d69154

import Mathlib
import Definitions.Def_SIBrochure_units

set_option autoImplicit false

open SIBrochure in
theorem solution :
    mole = (6.02214076e23 : ℝ) • NA⁻¹ := by
  ext <;> simp [NA, mole, base, unitOf] <;> first | ring1 | norm_num
