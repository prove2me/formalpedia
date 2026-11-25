-- Prove2me | solution 1 for SZ.isDigits_digitB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:31.424804+00:00
-- url     : https://prove2.me/submissions/143088e7-bdec-40f1-bbf6-ce9652c3fa76

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_digitB_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution : IsDigits 3 digitB :=
  { two_le := by norm_num
    nonneg := fun i => by rcases digitB_mem i with h | h <;> omega
    le_sub_one := fun i => by rcases digitB_mem i with h | h <;> omega }
end SZ
