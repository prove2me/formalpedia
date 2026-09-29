-- Prove2me | solution 1 for SenTachyon.twoBraneMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T23:17:11.200835+00:00
-- url     : https://prove2.me/submissions/1ca524ed-e927-4b69-a345-53ebc02c490c

import Mathlib
import Definitions.Def_SenTachyon_Defs

set_option autoImplicit false

open SenTachyon in
theorem solution (R₁t R₂t gt : ℝ) (h₁ : 0 < R₁t) (h₂ : 0 < R₂t) (hg : 0 < gt) :
    twoBraneMass R₁t R₂t gt = 2 * R₁t * R₂t / gt := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hg' : gt ≠ 0 := hg.ne'
  unfold twoBraneMass dbraneTension torusArea
  field_simp
