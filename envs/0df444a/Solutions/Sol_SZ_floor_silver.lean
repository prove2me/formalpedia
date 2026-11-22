-- Prove2me | solution 1 for SZ.floor_silver
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:09.93412+00:00
-- url     : https://prove2.me/submissions/e3250c19-e623-44f1-ab43-4f9764d36860

import Definitions.Def_SZ_PellDesign
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_SZ_Silver
import Theorems.Thm_SZ_silver_pair
import Theorems.Thm_SZ_silver_conj_neg
import Theorems.Thm_SZ_xiDesign_silver
import Theorems.Thm_SZ_floorNeg


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution (n : ℕ) :
    ⌊(2 - Real.sqrt 2) / 4 * (1 + Real.sqrt 2) ^ n⌋
      = rec2 2 1 1 0 n - (if n % 2 = 0 then 1 else 0) := by
  rw [← xiDesign_silver]
  exact floorNeg silver_pair silver_conj_neg n
end SZ
