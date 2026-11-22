-- Prove2me | solution 1 for SZ.strace_emod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:49:47.101626+00:00
-- url     : https://prove2.me/submissions/20d64454-115d-46f6-ad73-a9c0e5897a15

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_QuadThm6
import Theorems.Thm_SZ_rec2_add_two
import Theorems.Thm_SZ_twoStep


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) : rec2 2 2 2 2 n % 6 = 2 := by
  induction n using SZ.twoStep with
  | h0 => decide
  | h1 => decide
  | hs n ih1 ih2 => rw [rec2_add_two]; omega
end SZ
