-- Prove2me | solution 1 for SZ.one_lt_sqrt_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:50.615452+00:00
-- url     : https://prove2.me/submissions/0c9167d4-36e7-4f8c-bcac-e23567fcabcd

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_SqrtTwo

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : (1 : ℝ) < Real.sqrt 2 := by
  have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h
end SZ
