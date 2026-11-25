-- Prove2me | solution 1 for SZ.witXi_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:36:12.532801+00:00
-- url     : https://prove2.me/submissions/ea3b4962-7868-49b8-8acd-0a3851d0f12b

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
import Definitions.Def_SZ_SqrtThree
import Theorems.Thm_SZ_witXi_mem

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : 0 < witXi := lt_of_lt_of_le (by norm_num) witXi_mem.1
end SZ
