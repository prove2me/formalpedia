-- Prove2me | solution 1 for SZ.witX_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:51.947221+00:00
-- url     : https://prove2.me/submissions/e5392c11-f21e-4158-a44c-5212c7cdfcf8

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_digitReal_le_one
import Theorems.Thm_SZ_digitReal_nonneg
import Theorems.Thm_SZ_isDigits_digitA


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : 0 ≤ witX ∧ witX ≤ 1 :=
  ⟨digitReal_nonneg isDigits_digitA, digitReal_le_one isDigits_digitA⟩
end SZ
