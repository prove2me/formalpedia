-- Prove2me | solution 1 for SZ.digitY_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:26.37128+00:00
-- url     : https://prove2.me/submissions/1180c770-8835-48e0-a16f-e67d814b375c

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitY_mem

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution (i : ℕ) : Even (digitY i) := by
  rcases digitY_mem i with h | h <;> rw [h] <;> decide
end SZ
