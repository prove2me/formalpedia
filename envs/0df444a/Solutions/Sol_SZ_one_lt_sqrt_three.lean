-- Prove2me | solution 1 for SZ.one_lt_sqrt_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:56.784774+00:00
-- url     : https://prove2.me/submissions/41c8b4ba-9779-4f6e-9a74-c550c85b5538

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : (1 : ℝ) < Real.sqrt 3 := by
  have h : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h
end SZ
