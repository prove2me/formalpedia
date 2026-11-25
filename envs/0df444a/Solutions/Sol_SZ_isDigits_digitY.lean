-- Prove2me | solution 1 for SZ.isDigits_digitY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:14:28.985457+00:00
-- url     : https://prove2.me/submissions/29a9e523-e4e7-4376-96d6-1e998a8ac636

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitY_mem

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : IsDigits 3 digitY :=
  { two_le := by norm_num
    nonneg := fun i => by rcases digitY_mem i with h | h <;> omega
    le_sub_one := fun i => by rcases digitY_mem i with h | h <;> omega }
end SZ
