-- Prove2me | solution 1 for SZ.isDigits_digitA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:29:45.009922+00:00
-- url     : https://prove2.me/submissions/964344da-d847-4295-939d-676cef88c647

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_digitA_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution : IsDigits 3 digitA :=
  { two_le := by norm_num
    nonneg := fun i => by rcases digitA_mem i with h | h <;> omega
    le_sub_one := fun i => by rcases digitA_mem i with h | h <;> omega }
end SZ
