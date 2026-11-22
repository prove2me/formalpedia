-- Prove2me | solution 1 for SZ.floor_silver_pell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:55:10.455077+00:00
-- url     : https://prove2.me/submissions/8907d75e-d99b-4e77-bb12-d66659c6a1e9

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
import Theorems.Thm_SZ_rec2_two_one_succ
import Theorems.Thm_SZ_floor_silver

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) :
    ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ (n + 1)⌋
      = pell n - (if n % 2 = 0 then 0 else 1) := by
  rw [floor_silver, rec2_two_one_succ]
  congr 1
  rcases Nat.even_or_odd n with he | ho
  · have : n % 2 = 0 := Nat.even_iff.mp he
    rw [if_neg (by omega), if_pos this]
  · have : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_pos (by omega), if_neg (by omega)]
end SZ
