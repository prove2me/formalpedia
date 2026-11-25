-- Prove2me | solution 1 for SZ.witY_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:45.016337+00:00
-- url     : https://prove2.me/submissions/b3a67505-04c2-4f40-8516-e98d6ba9a64b

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitReal_compl
import Theorems.Thm_SZ_isDigits_digitB


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : witY = 1 - digitReal 3 digitB := by
  have hfun : (fun i => ((3 : ℕ) : ℤ) - 1 - digitB i) = digitY := by
    funext i
    simp only [digitY]
    norm_num
  rw [witY, ← hfun, digitReal_compl isDigits_digitB]
end SZ
