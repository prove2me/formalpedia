-- Prove2me | solution 1 for SZ.irrational_sqrt_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:27:54.915649+00:00
-- url     : https://prove2.me/submissions/3b65ec80-5ec9-4b76-8d45-14fea8a4056c

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution : Irrational (Real.sqrt 3) := by
  have h : Nat.Prime 3 := Nat.prime_three
  simpa using h.irrational_sqrt
end SZ
