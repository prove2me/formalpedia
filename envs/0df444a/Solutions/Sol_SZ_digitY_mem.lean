-- Prove2me | solution 1 for SZ.digitY_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:58.331412+00:00
-- url     : https://prove2.me/submissions/302f109b-76d0-4684-98ac-51d6fe33a4e9

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitB_mem


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (i : ℕ) : digitY i = 0 ∨ digitY i = 2 := by
  rcases digitB_mem i with h | h <;> simp [digitY, h]
end SZ
