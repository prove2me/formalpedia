-- Prove2me | solution 1 for SZ.rec2_two_one_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:53:13.464313+00:00
-- url     : https://prove2.me/submissions/a0dd8177-716f-4f81-a4fc-493e50b7e761

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
import Theorems.Thm_SZ_pell_add_two
import Theorems.Thm_SZ_rec2_add_two
import Theorems.Thm_SZ_twoStep


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) : rec2 2 1 1 0 (n + 1) = pell n := by
  induction n using SZ.twoStep with
  | h0 => rfl
  | h1 => rfl
  | hs n ih1 ih2 =>
    rw [show n + 2 + 1 = (n + 1) + 2 from rfl, rec2_add_two, pell_add_two, ih1, ih2]
    ring
end SZ
