-- Prove2me | solution 1 for SZ.irrational_sqrt_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:33.385492+00:00
-- url     : https://prove2.me/submissions/5ae139a1-304b-46db-b660-52c142ae0242

import Definitions.Def_SZ_Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.NormNum.Prime
import Definitions.Def_SZ_GoldenS

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution : Irrational (Real.sqrt 5) := by
  have h := (by norm_num : Nat.Prime 5).irrational_sqrt
  simpa using h
end SZ
